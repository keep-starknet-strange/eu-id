# A-003 — mdoc slow gate red after Q-002: Sha256Prover lacked partial preprocessed writes

Recorded: 2026-07-04 (fable, main session — found during the s4-lite coprocessor merge gates)

## Symptom
`isolated_mdoc_circuit_profile_proves_and_verifies` (release, ignored) panicked at
`air-core/src/lib.rs:320`: "module does not support partial preprocessed writes",
`left: []` vs the full SHA preprocessed id list.

## Root cause
The Q-002 fix (`16d03fde`) gave `Sha256Prover` fingerprints, which let the
orchestrator's cross-instance dedup detect the four mdoc SHA instances as
duplicates — so instances 2–4 are asked to write their non-duplicate subset
(empty). `Sha256Prover` never overrode `write_selected_preprocessed`, so the
trait default's full-match assert fired. Q-002's verification ran the nonce and
stwo-sha256 suites but not the mdoc slow gate (single SHA instance ⇒ never
partial ⇒ the gap was invisible there). Not caused by the coprocessor merge —
confirmed the merge changeset touches neither air-core, stwo-sha256, nor mdoc.

## Fix
`Sha256Prover::write_selected_preprocessed` implemented, mirroring
`P256Prover`'s: full-list fast path, else filter the generated/caller evals by
the selected ids (empty selection writes nothing).

## Verification
- mdoc slow gate: 1 passed (2.0 s — faster now that 3 duplicate SHA
  preprocessed writes are actually skipped).
- nonce slow gate: 7 passed. mdoc_support fast: 22 passed. stwo-sha256 suite,
  fmt, clippy: green.

## Lesson (for gate lists)
Any change to preprocessed identity/dedup behavior must run BOTH slow gates —
the nonce monolith exercises single-instance SHA, only the mdoc circuit
exercises multi-instance dedup.
