# TS13 phone proving campaign decisions

Status: active

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

The campaign uses a hybrid route:

- The AIR track reviews and measures the committed-nibble candidate now.
- The engine track may develop an uncommitted-MLE opening primitive later.
  That work does not move the STWO pin or block the AIR candidate.

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

The prior 25-row all-ML-DSA-65 carrier used 9,102,656 committed cells. The
layered acceptance candidate replaces that carrier. Its current Keccak
AIR-reference count is 1,534,720 cells.

A-015-review accepts the candidate as sound and reports no critical or high
finding. Final acceptance requires its three completion conditions, a new
source-bound artifact, the full release matrix, and the final-hash phone run.

### P3 — Private SHA-256

The retained private MSO, item, and shared SHA table geometry uses 1,320,640
cells. It keeps the private-input checks inside the proof.

### P4 — PCS and FRI

The selected point is blowup 3, 36 queries, proof-of-work 20, and lifting log
size 19. The current candidate envelope is 1,507,374 bytes.

### P5 — Android runtime

The selected runtime uses six Rayon workers, a 2 MiB proof-thread stack, a
16 MiB proof-worker stack, and no affinity policy. The jemalloc candidate was
rejected. The exact AArch64 library uses the intended NEON path.

### P6 — Structural continuation

The fixed-scope witness-parallelism route was rejected because it could not
meet the three-phone gate. Structural AIR work was then authorized with all
properties in section 2 intact.

## 5. Current layered candidate

A-013 quarantined the committed-nibble implementation and selected a
committed-bit v3 route. A-015 suspends that v3 route and promotes the existing
committed-nibble implementation to an acceptance candidate. The bit layer is
internal. It is deterministically extracted from 400 committed spread-nibble
columns. Both boundary claims tie back to committed columns.

The soundness review is complete. Final acceptance requires all of these
events:

1. Complete the F-1 artifact-binding wording, F-2 exported off-domain nibble
   negative, and F-3 carrier-baseline wording.
2. Commit the source change and generate a new source-bound artifact.
3. Pass the complete release matrix with the new circuit hash.
4. Pass the exact three-phone Firebase matrix with that hash.

The reviewed pre-F-2 candidate has this provenance:

- Design: `docs/ts13-keccak-layered-gkr.md`.
- Soundness-source commit: `2111a1eb`.
- Source-bound artifact commit: `5a619bf2`.
- Evidence-ledger commit: `358646b1`.
- Circuit hash:
  `3fac167754de85508fd6fda45e37043f6e104821463b9fa40e17d88fa4938b9c`.
- Replacement geometry: 212,992 cells.
- Complete Keccak AIR-reference geometry: 1,534,720 cells.
- Proof body capacity: 1,507,328 bytes.
- Total envelope: 1,507,374 bytes.

Conditions F-1 through F-3 are complete at soundness-source commit
`cf8f2cec`. The regenerated circuit hash is
`c7c99e7b6e7cddbfc27617b2597bea1315ebd39e34ed08c564d67220282af9bc`.
The shape and 1,507,328-byte proof-body capacity are unchanged. The final
package and performance evidence are pending.

The current desktop median is 1,784 ms for proving and 80 ms for verification.
Peak resident memory is 777,682,944 bytes. These values are a throughput
checkpoint only. F-2 changes the soundness source and makes circuit-hash
rotation mandatory. Regenerate the artifact, fixture, AAR, and APKs. Then
rerun the full release, ignored, negative, unlinkability, artifact, and phone
test sets.

## 6. Review gates

A-016 withdraws the stale literal 108-bit soundness label. The retained OODS
term is about 106 bits by itself. The named live partial union is about 105.91
bits before global LogUp collision terms. A-015-review confirms that the
candidate replaces the removed carrier contribution without a net loss under
the same accounting convention. It reports no omitted term class or changed
term outside the replacement.

A-016 also retires the earlier A54 complete-Keccak limit of 1,200 ms because
the timing wire cannot measure it. The full cold `proveIdentity` result on all
three phones is the acceptance gate. Attach the desktop 25-phase record to the
same evidence set so that the layered prover cost stays visible.

Firebase remains on hold until an `A-014-confirmed` note records the user's
refreshed end-user OAuth login. After that note, probe the exact result bucket
before upload and run one matrix with all three phones.

## 7. Completion rule

One accepted, source-bound artifact must meet the 2,000 ms cold-prove limit on
all three phones. Do not call the performance campaign complete before that
result. If a phone misses the limit, continue with an accepted optimization or
obtain an explicit tracked gate change. Do not weaken the theorem,
unlinkability, ML-DSA-65, local proving, or the product API.
