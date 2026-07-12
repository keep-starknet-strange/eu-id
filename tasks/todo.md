# Quantum-safe-only proving campaign

Branch: `feat/quantum-safe`
Baseline: `ce26b934` (S9)

## Milestone Q1 — branch divergence

- [x] Publish the clean S9 branch baseline to `origin/feat/quantum-safe`.
- [x] Audit branch features, classical dependencies, SHA consumers, and campaign floors.
- [ ] Remove P-256/ec-coprocessor crates from the quantum branch workspace and product manifests.
- [ ] Make ML-DSA/quantum-safe the unconditional product build; remove obsolete product feature aliases.
- [ ] Convert the performance probe and dependency gate to the branch's default quantum build.
- [ ] Delete dormant P-256/ec-coprocessor product code and proof fields from `eu-id-prover`, `sdk`, and `eu-id-ffi`.
- [ ] Run the focused quantum build/test/dependency gates.
- [ ] Commit and push Q1.

## Milestone Q2 — remove the revocation SHA conveyor

- [ ] Make `MdocRevocationRangeBind` provide `HOSTED_MSG_FIELD_ID` bytes directly from its private
      `id_lo`/`id_hi` witness and public epoch.
- [ ] Keep every private byte range-pinned in AIR after the SHA provider is removed.
- [ ] Remove the revocation witness/slot/handles from the merged SHA prover and verifier.
- [ ] Add focused claimed-sum/tamper coverage and retain the full revocation privacy/e2e rail.
- [ ] Run focused tests, full quantum gates, shape dump, and single-thread A/B benchmark.
- [ ] Document measured cells/columns/proof/prove/verify changes.
- [ ] Commit and push Q2.

## Milestone Q3 — attribute-only small-load SHA

- [ ] Record the exact remaining attribute block/load distribution after Q2.
- [ ] Specify the replacement AIR, including degree worksheet, lookup/range strategy, transcript
      shape, adversarial cases, and old/new cell/column model.
- [ ] Implement the minimum sound attribute-only SHA design without changing shared
      `air-core`, `stwo-keccak`, or `stwo-mldsa` unless the design proves it necessary.
- [ ] Differential-test digests against `sha2` across production and boundary message lengths.
- [ ] Run adversarial constraint tests, full quantum gates, and same-session A/B benchmarks.
- [ ] Commit and push Q3.

## Campaign rails

- Do not edit the user's main checkout or classical branches.
- Do not touch `stwo-mldsa::coeffs`; its Horner interaction requires `bound == log + 1`.
- Preserve the local Stwo `8c998390` composition-split patch until an equivalent remote pin exists.
- Keep security at least 128 bits; production is `(1,4,26,2)` with PoW 25 (129-bit estimate).
- Compare performance only in the same worktree, feature set, build mode, and session.
- Push only coherent checkpoints whose focused gates pass.

## Review

In progress.
