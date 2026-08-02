# TS13 phone proving campaign decisions

Status: decision required; P5 is canonical and held

This file is the tracked authority for the TS13 phone proving campaign. The
files under the main checkout's `tasks/` directory are communication mirrors.
They are not campaign-branch records.

## 1. Goal

The campaign must make one cold `proveIdentity` call complete in less than
2,000 ms on each of these Android phones:

- Google Pixel 8, model `shiba`, API 34.
- Samsung Galaxy S24 Ultra, model `e3q`, API 34.
- Samsung Galaxy A54, model `a54x`, API 34.

The same execution must meet these limits:

- `verifyIdentity` must complete in at most 500 ms.
- The identity-proof envelope must contain at most 2,500,000 bytes.
- The envelope size and public input must not depend on the credential.

Use a fresh process and one proof for every cold measurement. Record the
source commit, circuit hash, artifact, and package hashes. Also record the
device, API level, worker count, stack sizes, proof time, verification time,
envelope size, and peak resident memory.

Performance is a campaign gate. It is not part of TS13 conformance.

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

## 3. Approved change ledger

The following values may change without another user question:

- Circuit hash.
- Proof-body composition.
- Envelope capacity, up to 2,500,000 bytes.
- Phone verification time, up to 500 ms.

Any other property change needs user approval before implementation.

Repository-owned `air-core` proving machinery is allowed. The STWO pin does
not move under this authorization.

The campaign uses this route:

- The restored P5 carrier is the canonical proof path.
- The c7 AIR track is sound but rejected on measured phone throughput.
- A-019 supersedes the A-018 engine authorization. It rejects the compact
  authenticated-MLE route under the fixed campaign constraints.
- No engine, N, S, repin, or application-integration work may start before
  Lucas selects a new campaign disposition.
- The application STWO pin stays at `4f39939e`.

A filed `GO` starts an approved stage. Fable controls technical mailbox
answers and stage-gate definitions. Lucas may veto any campaign decision.

## 4. Work-order record

### P0 — Measurement

The canonical path reports bounded phase timing, worker settings, stack
settings, and peak memory. The Android test emits one summary record and 25
ordered phase records.

### P1 — Canonical-path overhead

The accepted checkpoint measured the canonical path at 1.059 times the
AIR-core time on desktop. This passed the 1.15 limit. The final accepted
artifact must record this ratio again or state why the checkpoint remains
applicable.

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

The campaign has no authorized P6 implementation route. Lucas must select one
of these dispositions:

1. Close the performance campaign at the verified P5 baseline.
2. Revise the phone-latency gate or another fixed campaign constraint.
3. Authorize a research-scale proof-system project outside this campaign.

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

## 6. Current gates

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

## 7. Completion rule

One accepted, source-bound artifact must meet the 2,000 ms cold-prove limit on
all three phones. The current campaign did not reach this limit, and A-019
confirms that no authorized implementation route remains. Hold the verified
P5 artifact until Lucas selects a disposition. Do not weaken the theorem,
unlinkability, ML-DSA-65, local proving, or the product API without an explicit
new decision.
