# Quantum-safe-only proving campaign

Branch: `feat/quantum-safe`
Baseline: `ce26b934` (S9)

## Milestone Q1 — branch divergence

- [x] Publish the clean S9 branch baseline to `origin/feat/quantum-safe`.
- [x] Audit branch features, classical dependencies, SHA consumers, and campaign floors.
- [x] Remove P-256/ec-coprocessor crates from the quantum workspace and downstream product manifests.
- [x] Remove the final internal scheme aliases/cfg branches from `eu-id-prover` and delete the
      excluded classical crate directories.
- [x] Convert the performance probe and dependency gate to the branch's default quantum build.
- [x] Delete the legacy identity/nonce/coprocessor product API, SDK/FFI ABI, mobile UI, benches, and tests.
- [x] Run the focused quantum build/test/dependency/lint gates.
- [x] Commit and push Q1 in coherent checkpoints (initial product split, internal collapse, and final
      physical divergence).

## Milestone Q2 — remove the revocation SHA conveyor

- [x] Make `MdocRevocationRangeBind` provide `HOSTED_MSG_FIELD_ID` bytes directly from its private
      `id_lo`/`id_hi` witness and public epoch.
- [x] Keep every private byte range-pinned in AIR after the SHA provider is removed.
- [x] Remove the quantum revocation witness/slot/handles from the merged SHA prover and verifier.
- [x] Add a direct-provider message-tamper negative and retain the full revocation privacy/e2e rail.
- [x] Run focused tests, full quantum gates, shape dump, and single-thread benchmark.
- [x] Document measured cells/columns/proof/prove/verify changes.
- [x] Commit and push Q2 (`497348e6`).

## Milestone Q3 — attribute-only small-load SHA

- [x] Record the exact remaining attribute block/load distribution after Q2.
- [x] Specify the replacement AIR, including degree worksheet, lookup/range strategy, transcript
      shape, adversarial cases, and old/new cell/column model.
- [x] Implement the minimum sound attribute-only SHA design without changing shared
      `air-core`, `stwo-keccak`, or `stwo-mldsa` unless the design proves it necessary.
- [x] Differential-test digests against `sha2` across production and boundary message lengths.
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

- Default workspace dependency tree is quantum-only; the only matched `rfc6979` is the allowed
  Stwo `starknet-crypto` backend dependency.
- Quantum product surface removed 17k+ lines of legacy identity/P-256/coprocessor code, tests,
  benchmarks, ABI, and mobile UI.
- Q2 shape: merged SHA is 1,098 columns at log 9 (was 1,199 at log 10); revocation range is
  361 columns at log 4 because it now locally bit-pins the 16 private bound bytes.
- Q2 total is 7,317 committed columns versus S9's 7,290: SHA saves 101 columns, local range
  pinning adds 128, net +27. Measured proof 1,113,700 B (+4,428 B), prove 8,192 ms,
  verify 16 ms. This is a deliberate architecture simplification/prerequisite for Q3, not a
  performance win; Q3 must recover the small column regression along with the remaining target gap.
- Remaining Q1 work is the internal `eu-id-prover` cfg/type collapse and physical deletion of the
  three excluded classical crate directories. The shipped default product/API/build graph no longer
  exposes them.
- Second Q1 checkpoint removes the legacy P-256/standalone-SHA/validity/payload assembly from the
  product prover and verifier, deletes the 800-line `mdoc_validity` AIR, and reduces the active mdoc
  window binder from 76 to 70 preprocessed columns by retaining only attribute constant windows.
- Verification for that checkpoint: workspace check and strict all-target clippy pass; all 37 prover
  tests pass across four suites (335.26 s), and all 13 SDK tests pass. Two consecutive release probes
  measured 2,717/2,861 ms prove, 17/15 ms verify, and 1,108,810/1,109,450-byte proofs. These are
  same-session post-change observations, not an A/B attribution against the earlier S9 session.
- Final Q1 divergence removes all P-256/ec-coprocessor/ML-DSA selection cfgs and feature aliases,
  makes ML-DSA unconditional in prover/SDK/FFI manifests, deletes 143 files across the three
  classical crate trees, removes their workspace exclusions, and regenerates `Cargo.lock` without
  the classical packages.
- Final Q1 verification: workspace all-target check, workspace strict clippy, and workspace fmt pass;
  37 prover tests pass (393.84 s), plus 13 SDK and 2 FFI tests. The broader debug workspace test
  umbrella was interrupted after exceeding 20 minutes without emitting a result; the product-scoped
  acceptance rails above completed cleanly.
- Q3 core replaces per-yield field selectors with one selector per target block and deletes the
  redundant split-pack representation now superseded by the hybrid boolean-bit AIR: 56 consumer
  trace columns, 24 consumer lookup sites, and eight 2^16-row table producers are gone. The merged
  production SHA model falls from 1,098 to 951 columns at log 9; the table deletion saves 8,429,568
  committed cells before the additional 34,304-cell selector saving.
- Q3 core verification: workspace all-target check, strict all-target clippy, formatting, and all
  148 active `stwo-sha256` tests pass (19 explicitly ignored). Differential vectors include the
  85-byte nationality and 92-byte birth-date production payload lengths plus SHA padding boundaries.
