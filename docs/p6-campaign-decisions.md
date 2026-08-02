# TS13 phone proving campaign decisions

Status: closed at P5 by A-020, 2026-08-02

This file is the tracked authority for the TS13 phone proving campaign. The
files under the main checkout's `tasks/` directory are communication mirrors.
They are not campaign-branch records.

## 1. Goal

The original campaign target was one cold `proveIdentity` call in less than
2,000 ms on each of these Android phones:

- Google Pixel 8, model `shiba`, API 34.
- Samsung Galaxy S24 Ultra, model `e3q`, API 34.
- Samsung Galaxy A54, model `a54x`, API 34.

The same execution had these additional limits:

- `verifyIdentity` must complete in at most 500 ms.
- The identity-proof envelope must contain at most 2,500,000 bytes.
- The envelope size and public input must not depend on the credential.

Use a fresh process and one proof for every cold measurement. Record the
source commit, circuit hash, artifact, and package hashes. Also record the
device, API level, worker count, stack sizes, proof time, verification time,
envelope size, and peak resident memory.

Performance is a campaign gate. It is not part of TS13 conformance.
A-020 formally retires the 2,000 ms target and closes the campaign at P5.
The verification, envelope, privacy, and soundness requirements remain met.

## 2. Properties that must stay unchanged

Every stage must preserve these properties:

- The theorem is the fixed TS13 age-over-18 identity theorem.
- The issuer, device, revocation, validity, claim, and request context remain
  inside the proof.
- The issuer, device, and revocation signatures use ML-DSA-65. ML-DSA-44 is
  prohibited.
- The public input remains unlinkable between presentations.
- Proving remains local.
- `proveIdentity` and `verifyIdentity` remain the only application proof API.
- The proof envelope remains fixed-size and credential-independent.
- The pinned STWO revision, PCS, and transcript stay unchanged unless a later
  tracked decision authorizes a change.
- STWO is not zero knowledge. Transcript zero knowledge remains future work.
- Algebraic soundness must stay unchanged or improve under the same accounting
  convention. The recorded live baseline is about 105.91 bits before global
  LogUp collision terms.

A STWO revision change needs proof-byte parity evidence, a demo-baseline
guard, and a separate authorization.

## 3. Historical change ledger

During the active campaign, these values could change without another user
question:

- Circuit hash.
- Proof-body composition.
- Envelope capacity, up to 2,500,000 bytes.
- Phone verification time, up to 500 ms.

Any other property change needed user approval before implementation.

Repository-owned `air-core` proving machinery was allowed. The STWO pin did
not move under this authorization.

The campaign ended with this route record:

- The restored P5 carrier is the canonical proof path.
- The c7 AIR track is sound but rejected on measured phone throughput.
- A-019 supersedes the A-018 engine authorization. It rejects the compact
  authenticated-MLE route under the fixed campaign constraints.
- A-020 closes the campaign at P5. It does not authorize an engine, N, S,
  repin, or application-integration performance track.
- The application STWO pin stays at `4f39939e`.

During the active work, a filed `GO` started an approved stage. Fable
controlled technical mailbox answers and stage-gate definitions. Lucas could
veto any campaign decision. A-020 ends these authorizations. Future work needs
a new tracked decision.

## 4. Work-order record

### P0 — Measurement

The canonical path reports bounded phase timing, worker settings, stack
settings, and peak memory. The Android test emits one summary record and 25
ordered phase records.

### P1 — Canonical-path overhead

The accepted checkpoint measured the canonical path at 1.059 times the
AIR-core time on desktop. This passed the 1.15 limit. A-020 accepts this
checkpoint as the closing P1 evidence. It requires no new ratio measurement.

### P2 — Keccak service

The canonical 25-row all-ML-DSA-65 carrier uses 9,102,656 committed cells.
The c7 experiment reduced the Keccak AIR-reference count to 1,534,720 cells.
A-015-review accepts c7 as sound and reports no critical or high finding. The
final phone matrix rejected it for throughput. A-018 then restored P5.

### P3 — Private SHA-256

The retained private MSO, item, and shared SHA table geometry uses 1,320,640
cells. It keeps the private-input checks inside the proof.

### P4 — PCS and FRI

The selected point is blowup 3, 36 queries, proof-of-work 20, and lifting log
size 19. The canonical P5 envelope is 1,572,910 bytes.

### P5 — Android runtime

The selected runtime uses six Rayon workers, a 2 MiB proof-thread stack, a
16 MiB proof-worker stack, and no affinity policy. The jemalloc candidate was
rejected. The exact AArch64 library uses the intended NEON path.

### P6 — Structural continuation

The fixed-scope witness-parallelism route could not meet the three-phone gate.
The c7 structural AIR route was sound but slower on every binding phone. P5 is
therefore the canonical no-regression baseline.

A-019 confirms that the proposed compact authenticated-MLE route is blocked.
The P5 carrier commits 7,454,720 cells. Committing only the 200 state columns
would reduce that count by more than 5 million cells, but it would leave 696
nonlinear auxiliary MLEs unauthenticated. The nonlinear split operations do
not commute with MLE evaluation over the spread-byte representation. The
bit-or-nibble representation authenticates the derivation but recreates the
measured c7 dependent chain. The pinned PCS has no separate compact opening
that closes this gap. G1 also counts every field element committed by a
replacement proof system, so moving commitments does not meet the gate.

The campaign has no authorized P6 implementation route. A-020 selects closure
at the verified P5 baseline. A characteristic-2-native proof system would be
a separate research project and needs a new decision.

## 5. Current canonical P5 and archived c7

A-018 restored the last sound P5 proof path. The restored circuit has this
provenance:

- Source restore commit:
  `1e035312a566a2b8b96f4febad7eb35f17bed493`.
- Artifact and fixture commit:
  `cdfdf52c38a86143733ea80e4e8a3064a53950f9`.
- Circuit and artifact SHA-256:
  `6b30e79449d331477027412fd30c831f7bb45cea42214b072845173fea0241b6`.
- Soundness-source-tree SHA-256:
  `a39bc90c4c14226728bfd4f4a314a12a81f162c8fd62991fc5f214973de99ec3`.
- Shape-manifest SHA-256:
  `a5c8c6fdbaac8e1a9b0ca81704b31c7e29f2ec27487f603139531c39faf42d60`.
- Generation-input SHA-256:
  `60f05b9e596a48e03f6895f36f962775f3f6d1f2dfd50ca3fbb94640153863f0`.
- Mobile-fixture SHA-256:
  `06ef4ade577e1b69a776adafa778fd0fe16e3c75478772f1d5abf0c7072a98f4`.
- Cargo.lock SHA-256:
  `23e70c964b943632fed547cfa38e6c1d24cfeac070a3518bc0f1a704f7597dbe`.
- Proof-body capacity: 1,572,864 bytes.
- Total envelope: 1,572,910 bytes.

The historical P5 matrix `matrix-92u1aei93c81a` is the A-018 phone-latency
baseline. It measured 5,450 ms on Pixel 8, 2,755 ms on Galaxy S24 Ultra, and
5,853 ms on Galaxy A54. It used the prior P5 circuit hash `2eff9e07...`. It is
not current-hash evidence.

The c7 status is: sound; rejected on measured phone throughput, 2026-08-02

Its final matrix measured 13,560 ms, 5,075 ms, and 9,523 ms on the same
phones. The complete c7 evidence remains in
`tasks/bench-results/ts13-layered-final-20260802`.

## 6. Closing evidence

A-016 withdraws the stale literal 108-bit soundness label. The retained OODS
term is about 106 bits by itself. The named live partial union is about 105.91
bits before global LogUp collision terms. The c7 soundness review found no
omitted term class and no changed term outside the replacement.

The fresh restored-P5 desktop record measured `proveIdentity` at 1,280 ms and
`verifyIdentity` at 42 ms. Peak resident memory was 1,513,652,224 bytes. The
run used circuit `6b30e794...`, six proof workers, a 2 MiB proof-thread stack,
16 MiB worker stacks, and a fixed 1,572,910-byte envelope. It emitted 25 phase
rows.

A-018-route defined these engine gates:

1. G1: On desktop at product size, the primitive-backed Keccak proof must beat
   the P5 post-proof phase and remove at least 5 million committed cells.
2. G2: On all three phones, the post-proof phase must not exceed P5 and total
   proving must be strictly faster than P5.

A-019 closes this route before G1 because no sound primitive meets its cell
and dependency requirements. N, S, and application integration remain
stopped. Do not run G2 against a design that did not pass G1.

The closing phone benchmark passed verification at or below 500 ms, used a
fixed 1,572,910-byte envelope, and returned one successful test on each phone.
It did not meet 2,000 ms proving. A-020 retires that proving target.

## 7. Closure rule

A-020 closes P1 through P6 as applicable at the restored P5 baseline. P1
through P5 produced accepted measurements and changes. P6 mapped the measured
P5-to-c7 frontier and found no sound implementation route under the fixed
constraints. Section 11.7 of the normative specification defines the required
resource fields. The final conforming record is in section 8 below.

No campaign work remains. A future performance project needs a new tracked
decision. It must not weaken the theorem, unlinkability, ML-DSA-65, local
proving, or the product API without explicit authorization.

## 8. A-020 final disposition

Lucas closed the performance campaign at P5 on 2026-08-02. The canonical
circuit remains `6b30e79449d331477027412fd30c831f7bb45cea42214b072845173fea0241b6`.
The privacy claim remains `public-input unlinkable; transcript zero knowledge
pending`. The c7 and authenticated-MLE routes remain archived evidence. They
are not active implementation paths.

The closing P5 state passed all normal release workspace tests, all 18 ignored
release tests, the A1/A2/B unlinkability test, the invalid-witness matrix, the
source-bound artifact drift test, release Clippy with warnings denied, and
formatting. The per-work-order deltas and decisions remain in main-repository
mailbox Q/A-001 through Q/A-019. Git history retains c7, the superseded
A-018-route engine work order, the retired gates, and the complete design
review thread.

### Section 11.7 resource record

This tracked record supplies the fields required by section 11.7 of the
normative specification. The canonical restored artifact has this identity:

- source restore commit:
  `1e035312a566a2b8b96f4febad7eb35f17bed493`;
- artifact and fixture commit:
  `cdfdf52c38a86143733ea80e4e8a3064a53950f9`;
- circuit hash:
  `6b30e79449d331477027412fd30c831f7bb45cea42214b072845173fea0241b6`;
- fixture SHA-256:
  `06ef4ade577e1b69a776adafa778fd0fe16e3c75478772f1d5abf0c7072a98f4`;
- fixture path:
  `mobile/EuIdBenchAndroid/src/androidTest/assets/ts13_mobile_benchmark_fixture_v1.json`;
- release probe binary SHA-256:
  `3760907c6c4754e1941b4ea8dd61dc589a4a2df62f6f7b0b57af571906f8145a`;
- PCS: proof-of-work 20, blowup log 3, 36 queries, last-layer log 1,
  fold step 2, and lifting log 19;
- feature set: the default features of all six workspace packages;
- identity-proof envelope: 1,572,910 bytes.

One fresh release process on a 12-core Apple M2 Max with macOS 26.5.2 used
six proof workers, a 2,097,152-byte proof-thread stack, and 16,777,216-byte
worker stacks. It completed `proveIdentity` and `verifyIdentity`, emitted 25
phase records, and measured 1,280 ms for proving, 42 ms for verification, and
1,513,652,224 bytes of maximum resident memory.

The closing phone benchmark is Firebase matrix `matrix-92u1aei93c81a`.
Each phone ran Android 14, API 34, with six actual proof workers. Each run
used a 2,097,152-byte proof-thread stack, a 16,777,216-byte worker stack, and
the fixed 1,572,910-byte envelope.

| Device | Prove | Verify | Peak resident memory |
| --- | ---: | ---: | ---: |
| Google Pixel 8 (`shiba`) | 5,450 ms | 239 ms | 1,346,468 KiB |
| Samsung Galaxy S24 Ultra (`e3q`) | 2,755 ms | 140 ms | 1,414,276 KiB |
| Samsung Galaxy A54 (`a54x`) | 5,853 ms | 255 ms | 1,338,168 KiB |

All three phone tests passed. The matrix numeric ID is
`4904946063125125660`, and its history is `bh.f5f036aa81c4230a`. The matrix
used package commit `a91085dc` and fixture SHA-256
`c9fe96c76b13a884afb324e68dd939561c8d4664fe59e8cdfc85e8bf0625ea52`.
The measured package files have these SHA-256 values:

- AAR:
  `cdd744130c540f8ba910843b2a0fafe482714b864c200c06ee375c7aa6f242fa`;
- host APK:
  `b126d7693abb8079b2412a0ba1590124f16252ed61449d96e0b86f5aec3e6766`;
- test APK:
  `050ddfca27695d32c1c6e1d563ec76a1f16ad2d9551f497e877e5cd839678ae3`;
- AAR and host APK ARM64 library:
  `aedf9b1e6213e6d0bc7bf5b2cd20e51a5908eee5cee844b7e11bbcf87533dc38`.

It used the prior P5 circuit hash
`2eff9e073151b4bce733516f4b6dd411b6d48ef5425fd93d41c64bedf524fea9`.
The restored P5 source bytes match that proof path, but the source-bound hash
changed. A-020 accepts this matrix as the closing same-path phone benchmark.
It is not current-hash phone evidence. The 2,000 ms proving target was not
met and is retired. Performance remains outside TS13 conformance.

### Campaign yield

The campaign started on 2026-07-31 using the 2026-07-30 phone measurements as
its baseline. The closing P5 results improve on that baseline:

| Device | Starting prove | Closing P5 prove |
| --- | ---: | ---: |
| Google Pixel 8 | 7,892 ms | 5,450 ms |
| Samsung Galaxy S24 Ultra | 4,081 ms | 2,755 ms |
| Samsung Galaxy A54 | 11,601 ms | 5,853 ms |

The fixed envelope decreased from 1,769,518 bytes to 1,572,910 bytes. The
physical circuit decreased from about 24.49 million cells to 16,722,320
cells. The P5-to-c7 measurements show that phone cost depends on dependent
sumcheck rounds and table churn, not only on committed-cell count. A new point
outside this frontier requires a separate proof-system project.
