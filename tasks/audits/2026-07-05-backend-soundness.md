# Backend soundness re-audit — 2026-07-05/06

Audited commit: `e9e3c007` (feat/proof-reductions HEAD). Trigger: June 10–12
audits declared stale (85 commits rewrote the audited surface). Scope: the
post-June backend — EC coprocessor, shared SHA tables, γ-digest/operand
dedup, FRI/PCS security accounting. Out of scope: mdoc v2 statement (audit
after Phase F merge), dense packing (NOT merged here — still on s4-lite).

## Verdict

**No CONFIRMED constraint-level or protocol-level break in any audited
surface.** The single live CRITICAL remains the pre-tracked verifier-side
preprocessed-root unpinning (F-ROOT below). Hardening backlog: 5 items.

## Confirmed-clean (with evidence in the session audit reports)

- **EC coprocessor** (first-ever audit): Ligero tuple in code == Q-027 claim,
  soundness sum recomputed = 2^-132.01 exactly; caller-input binding
  (verify_c1/c2/c3 + C14 r-gate + InputClaims MLE tie-in) survived an active
  bypass construction attempt; commit-then-challenge ordering verified for
  every transcript value; sumcheck round/degree/final-eval accounting clean;
  no free variables among opened values; V1_NON_ZK enforced and honest;
  layout constants alias-free; leaf hashes bind row indices.
- **Shared SHA tables**: provider/consumer relation identity verified
  (draw_with_shared_tables), union multiplicities sound (out-of-table use
  cannot cancel), consumer padding enabler-gated, only split_pack+range
  shared (no accidental sharing).
- **γ-digest / operand dedup**: digest is a degree-1 expression of
  already-constrained masks — no free column, operands cannot escape; γ
  drawn post-base-commit; tag+row_index anti-replay verified by tests.
- **Digest binding**: z == SHA-256(C) forced via matching yield/require over
  the same drawn relation; byte recomposition range-checked and active-gated.
- **PCS config pinning**: both verifiers reject prover-weakened configs
  (stwo-p256 proof/mod.rs:2758-2764; eu-id-prover lib.rs:1621-1630
  WeakConfig). Production paths compute to 128-bit profile
  (FriConfig::new(1,2,59,2)+pow10); WO-3.3 schedule change is folding-only,
  security arithmetic unaffected.

## Findings

| ID | Sev | Status | Finding | Where |
|---|---|---|---|---|
| F-ROOT | CRITICAL | **CLOSED 2026-07-07 @ d95aeb4f** (merge: fix/froot-pinning-complete e9676389, stacked on e221b0fc) — verifier pins the preprocessed root at all four absorb sites; negatives `current_p256_monolithic_verifier_pins_the_preprocessed_root` + `verify_identity_pins_the_preprocessed_root` green (release, 1-thread) | absorb sites: air-core lib.rs:469; stwo-p256 proof/mod.rs:2764; hinted_mul air.rs:1225; gkr_spike.rs:369/456/547 (feature-gated) |
| F-BENCH | HIGH (honesty) | CONFIRMED | BM_ShaZK_equiv runs 13-bit (PcsConfig::default) but perf-log labels "128-bit baseline"; ECDSA sibling rows genuinely 128-bit | longfellow_equiv.rs:38-41; perf-log.md L121-134 |
| F-BIAS | MED | PLAUSIBLE | Fp::random single conditional subtraction ⇒ ~2^-32 bias/draw; caps sumcheck-layer soundness below 128-bit, bound undocumented | ec-coprocessor field.rs:46-53 |
| F-SUM | LOW | PLAUSIBLE | unchecked u32 += in shared-table multiplicity union (completeness, release wraparound) | stwo-sha256 multiplicities.rs sum_multiplicity_vectors |
| F-PARAMS | LOW | verified-absent v1 | Ligero proximity transcript absorbs root but not params/committed_len; fine while params verifier-fixed, hole if v2 makes them prover-influenced | ecdsa.rs:1471-1505 |
| F-SWEEP | INFO | CONFIRMED | fri_sweep example pins pre-WO-3.3 schedule constants (last=5,fold=1); models a schedule production no longer uses | examples/fri_sweep.rs:17-20 |

## Fix guidance

- F-ROOT: verifier re-derives canonical preprocessed trace (or pins expected
  root constant per circuit shape) before commit; AND move the
  content-invariant fingerprint check into verify. One fix, both halves.
- F-BENCH: set explicit 128-bit PcsConfig in the SHA equiv bench (mirror the
  P256 sibling), re-run, rewrite the affected perf-log rows with security
  bits labeled per row.
- F-BIAS: rejection-sample Fp::random, or document the exact soundness debit
  with a computed bound.
- F-SUM: checked_add. F-PARAMS: absorb params+committed_len (cheap, do with
  F-BIAS). F-SWEEP: update constants.

## Freshness note

This audit covers e9e3c007 only. It does NOT cover: the mdoc v2 port branch
(phases A-D landing now), dense packing (s4-lite), or anything merged after
2026-07-06. Per tasks/lessons.md: re-check `git log --since` against this
date before citing.

## Addendum 2026-07-07 — F-ROOT closed; rayon deadlock recurrence

- F-ROOT CLOSED via merge d95aeb4f (branch fix/froot-pinning-complete). Both
  root-pin negatives green in release single-thread. F-PARAMS was separately
  closed inside the circle-FFT v3 params work (version-tagged params absorbed
  into the proximity transcript).
- OPERATIONAL FLAG: the rayon lost-wakeup deadlock RECURRED 2026-07-07 during
  the merge gates — stwo-p256 debug test binary (digest_bind bridge test) sat
  78 min at 0% CPU, all threads in __psynch_cvwait, while another session ran
  a 99%-CPU bench on the same machine. WO-1.7's fix is insufficient under
  cross-session CPU contention. Workaround: RAYON_NUM_THREADS=1 (and release
  mode) for gate runs. Needs re-investigation before trusting any parallel
  numbers collected on a shared machine.
