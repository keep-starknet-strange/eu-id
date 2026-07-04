# WO-M1 Coprocessor Mainline Merge

Source of truth: `/Users/lucas/eu-id/tasks/parity/s4/WO-M1-coprocessor-mainline-merge.md`.
Worktree: `/Users/lucas/eu-id/.claude/worktrees/wo-m1-coprocessor-merge` on `codex/wo-m1-coprocessor-merge`.
Base: `feat/proof-reductions@7af53303`.
Scope guard: implement feature-on coprocessor pipeline integration with default OFF. Do not flip `ec-coprocessor` into default features or retire `stwo-p256` until the Phase 3 architect ack exists.

## Preconditions / Drift

- [x] Read WO-M1, BL6, Q-017, Q-027, G3, current `eu-id-prover`, mdoc `PublicDigestBind`, and lessons.
- [x] Check main checkout status. Main is not quiet only because ignored task ledger rows are modified in `tasks/parity/STATUS.md`; the original "84-file mdoc track" blocker is stale.
- [x] Confirm Phase 1 crate landing is already in history: `40b57444 merge: eu-id-ec-coprocessor v1 (feature-gated, default off)`.
- [x] Confirm `s4-lite` worktree is clean at `66b16c03`.
- [x] Run precondition gate: `rtk proxy cargo test -p eu-id-ec-coprocessor`.
- [x] Run feature-off baseline gate after local changes: default proof path remains green and byte shape/default module order unchanged.

## Implementation Plan

- [x] Phase 2.1: promote mdoc's `PublicDigestBind` to a shared `crates/eu-id-prover/src/public_digest_bind.rs` module; do not fork/copy the component.
- [x] Phase 2.2: add seed-fork/rejoin transcript binding: absorb Q-017 statement into `air_core::Ch`, draw 32-byte seed, run coprocessor from `CoprocessorChannel::from_seed`, then rejoin with a hash of the serialized bundle.
- [x] Phase 2.3: delete `CoprocessorChannel::default()`/`Default` so unseeded coprocessor transcripts are unrepresentable.
- [x] Phase 2.4: under `ec-coprocessor`, change `prove_with_column_breakdown` to remove the credential P256 AIR module and replace the digest bridge with public-z digest bind. Keep the nonce P256 AIR module because WO-M1 Phase 4 explicitly says nonce retirement is a separate architect question.
- [x] Phase 2.5: update `Proof`/verifier reconstruction so feature-on proofs carry the public credential instance plus coprocessor bundle and rebuild SHA/public-digest-bind/predicates/nonce only.
- [x] Phase 2.6: fix feature-on tests for the current nonce-aware API and add negatives for missing/tampered/swapped coprocessor payload and public-z mismatch.
- [x] Phase 2.6: add/extend transcript-order tests for post-statement, post-seed, and post-rejoin digests; add negative tests for bundle-byte tamper and wrong statement/seed order.
- [x] Phase 2.7: run feature-on verification gates: `rtk proxy cargo test -p eu-id-prover --features ec-coprocessor` and focused ignored e2e if needed.
- [x] Phase 3 prep: append task/perf/status rows and mailbox the remaining campaign results only if the implemented feature-on path is green. Do not self-certify default flip.
- [x] Wait for `/Users/lucas/eu-id/tasks/parity/mailbox/answers/Q-M1-001.md` before removing the credential P256 AIR module.

## Phase 3 Campaign

- [x] Run G4-row/per-family coprocessor soundness suite: `rtk proxy cargo test -p eu-id-ec-coprocessor --release`.
- [x] Run full-bundle ignored coprocessor negatives: `rtk proxy cargo test -p eu-id-ec-coprocessor --release -- --ignored`.
- [x] Run feature-on normal CI target: `rtk proxy make test-ec-coprocessor`.
- [x] Run feature-on scheduled ignored CI target: `rtk proxy make test-ec-coprocessor-ignored`.
- [x] Run transcript-order focused guard after the full target: `rtk proxy cargo test -p eu-id-prover --features ec-coprocessor feature_gated_coprocessor_ -- --ignored`.
- [x] Take `tasks/parity/BENCH-LOCK` and run all Phase 3 perf gates with `RAYON_NUM_THREADS=1`.
- [x] Measure `identity_e2e/prove_identity` feature OFF and ON.
- [x] Measure proof bytes and verify time feature OFF and ON.
- [x] Write Phase 3 mailbox report with the v1 caveats and no default-on flip.
- [x] Commit Phase 3 task/report artifacts after verification.

## Review

- Current feature-on code is not Phase 2-complete: it proves the full P256 AIR path, then appends a coprocessor bundle after the STARK. Verifier checks both, so no P256 work is removed.
- Q-017 selects public statement binding for v1. Therefore the smallest Phase 2 bridge is a `PublicDigestBind` requiring SHA's digest bytes against the public credential `z`; no cross-field MAC or MLE argument is in scope.
- The existing mdoc `PublicDigestBind` is private inside `mdoc.rs`. Q-M1-001 rejects a forked copy; promote/import the component so mdoc and WO-M1 use one implementation.
- Nonce still uses `stwo-p256` in the monolithic proof today. Per WO-M1 Phase 4, deleting that AIR path is a STOP/architect question, so this implementation keeps `nonce_p256` in both feature modes.
- Precondition gate `rtk proxy cargo test -p eu-id-ec-coprocessor` passed: 84 executed tests passed, 12 ignored full-bundle tests remained ignored.
- Red baseline `rtk proxy cargo test -p eu-id-prover --features ec-coprocessor` fails to compile because feature-gated tests still call pre-nonce APIs.
- Filed `/Users/lucas/eu-id/tasks/parity/mailbox/questions/Q-M1-001-coprocessor-transcript-hook.md` because removing the credential P256 AIR while leaving `eu-id-ec-coprocessor` on its independent `CoprocessorChannel` would violate Q-017/BL6 shared-transcript order.
- Q-M1-001 answered: refactor first; no intermediate unbound feature path. Approved bridge is seed-fork + rejoin from `air_core::Ch`; delete unbound `CoprocessorChannel::default`; keep nonce P256 AIR; fix stale feature-on tests in this series.
- Coprocessor channel/API phase landed locally: `CoprocessorChannel::from_seed(seed, b"eu-id-ec-coproc-v1")` is now the only proof transcript constructor, standalone callers pass fixed test/bench seeds, and `rtk proxy cargo test -p eu-id-ec-coprocessor` passed with 84 executed tests and 12 ignored full-bundle tests.
- Promoted mdoc's `PublicDigestBind` into `crates/eu-id-prover/src/public_digest_bind.rs` and imported it from `mdoc.rs`; `rtk proxy cargo check -p eu-id-prover` passed on the default feature set.
- Feature-on identity proof now uses module order `nonce_p256, sha, public_digest_bind, age, nat, coprocessor`; the credential P256 AIR and scalar-z digest bridge are not in the `ec-coprocessor` module list. The coprocessor post-interaction hook absorbs the Q-017 statement/shape into `air_core::Ch`, draws the 32-byte seed, proves/verifies the bundle from that seed, then rejoins by mixing `Blake2s256(bincode(bundle))`.
- Feature-on `Proof` carries `credential_instances`, `public_digest_bind_interaction_claim`, and the coprocessor bundle instead of credential P256 claims. Nonce P256 claims remain unchanged.
- Added feature tests for nonce-aware APIs, missing bundle rejection, one-byte serialized bundle tamper rejection, fork/join prover-vs-verifier snapshots, and wrong seed-order rejection. For the seed checkpoint, the test records the drawn 32-byte seed because Stwo's `draw_u32s()` advances the draw counter without changing the channel digest.
- Verification passed: `rtk proxy cargo fmt --check`; `rtk proxy rg -n "impl Default for CoprocessorChannel|CoprocessorChannel::default" crates` returned no matches; `rtk proxy cargo test -p eu-id-ec-coprocessor` passed with 84 executed tests and 12 ignored full-bundle tests; `rtk proxy cargo test -p eu-id-prover` passed; `rtk proxy cargo test -p eu-id-prover --features ec-coprocessor` passed; focused ignored `feature_gated_coprocessor_fork_join_digests_match_prover_and_verifier -- --ignored` passed.
- Review follow-up fixed: CI now runs `make test-ec-coprocessor` on push/PR and `make test-ec-coprocessor-ignored` on the scheduled proof job, so default-off coprocessor hooks and ignored fork/join guards are compiled and executed mechanically. The Makefile owns both targets.
- Added two rejoin placement guards: `feature_gated_coprocessor_rejoin_changes_next_stark_challenge` and `feature_gated_coprocessor_rejoin_digest_changes_on_bundle_byte_tamper`.
- Mutation drill performed: temporarily made `mix_coprocessor_rejoin` a no-op, then `rtk proxy cargo test -p eu-id-prover --features ec-coprocessor feature_gated_coprocessor_rejoin_ -- --ignored` failed both rejoin guards. Restored the real rejoin and reran the same command successfully.
- Additional review follow-up verification passed: `rtk proxy cargo fmt --check`; `rtk proxy make test-ec-coprocessor`; `rtk proxy make test-ec-coprocessor-ignored`. `rtk proxy git diff --name-only | rg "^crates/stwo-p256"` returned no matches.
- Phase 3 found and fixed a default feature-off gate blocker before taking final measurements: `identity_e2e/prove_identity` and `identity_api::prove_identity_then_verify_identity_round_trips` panicked because the credential and nonce P256 modules shared witness-dependent hinted-mul schedule preprocessed ids. The nonce P256 module now uses the stable `nonce_p256` preprocessed namespace in both prover and verifier.
- Phase 3 soundness campaign passed: `rtk proxy cargo test -p eu-id-ec-coprocessor --release` (G4-row/per-family suite), `rtk proxy cargo test -p eu-id-ec-coprocessor --release -- --ignored` (12 full-bundle negatives), `rtk proxy make test-ec-coprocessor`, `rtk proxy make test-ec-coprocessor-ignored`, and focused `rtk proxy cargo test -p eu-id-prover --features ec-coprocessor feature_gated_coprocessor_ -- --ignored`.
- Phase 3 perf under BENCH-LOCK (`RAYON_NUM_THREADS=1`): Criterion `identity_e2e/prove_identity` feature OFF `3.2904 s` midpoint (`[3.2866, 3.2939] s`) vs feature ON `2.6246 s` midpoint (`[2.6168, 2.6321] s`), delta `-0.6658 s` / `-20.2%`.
- Phase 3 report-driver perf under BENCH-LOCK (`BENCH_ITERS=3`, `RAYON_NUM_THREADS=1`): `pipeline_e2e` feature OFF prove `4956 ms`, verify `39 ms`, proof `3,916,615` bytes; feature ON prove `3787 ms`, verify `41 ms`, proof `2,610,867` bytes. Proof-byte swing is `-1,305,748` bytes (`-1275.1 KiB`); verify swing is `+2 ms`.
- Phase 3 post-fix verification passed: `rtk proxy cargo fmt --check`, `rtk proxy cargo test -p eu-id-prover`, `rtk proxy cargo test -p eu-id-prover --test identity_api --release -- --ignored`, `rtk proxy make test-ec-coprocessor`, and `rtk proxy make test-ec-coprocessor-ignored`.
- Filed `/Users/lucas/eu-id/tasks/parity/mailbox/questions/Q-M1-002-coprocessor-phase3-report-default-flip-ack.md` with the Phase 3 report, measured perf gates, the nonce namespace blocker/fix, v1 caveats, and the default-on ack request. The default-on flip remains unapplied.

# Merge & Cleanup Plan

Source of truth: `tasks/merge-plan.md`.
Target checkout: `/Users/lucas/eu-id` on `feat/proof-reductions`.

- [x] M0: Re-verify worktree inventory before touching files.
- [x] M0: Write and commit the merge-freeze notice.
- [x] M1: Run the full pre-commit gate list once.
- [x] M1: Commit main checkout changes in the plan's grouped order.
- [x] M2: Merge `codex/full-mdoc-plan` if its worktree is clean; otherwise record skip.
- [x] M3: Merge `s4-lite` if its worktree is clean; otherwise record skip.
- [x] M4: Park GKR-v2 work, prune eligible stale worktrees, and remove the freeze notice.
- [ ] M5: Run final verification, update `tasks/parity/STATUS.md`, and report commits/skips.

## Review

- M0 inventory started 2026-07-04. Main checkout is on `feat/proof-reductions`.
- `codex/full-mdoc-plan` and `s4-lite` were dirty at inventory time, so their merge
  preconditions are not met unless they reach a clean quiet point before M2/M3.
- Freeze notice committed before M1 gates.
- M1 gates passed before grouped commits. Main checkout commits landed for mdoc,
  nonce monolith, mdoc perf, docs/tasks, and the WO sweep.
- M2 skipped: `codex/full-mdoc-plan` branch tip is already an ancestor, but its
  worktree remains dirty.
- M3 skipped: `s4-lite` branch tip is already an ancestor, but its worktree remains dirty.
- M4 parked SHA GKR implementation files on `spike/gkr-v2` at `1847bc06` and left
  active/dirty worktrees in place.
- M5 stopped on the final release nonce gate. Filed
  `tasks/mdoc-mailbox/questions/Q-002-final-merge-gate-preprocessed-fingerprints.md`.

# WO-A2 SHA Design-Space Sweep

Source of truth: `tasks/parity/WO-A2-sha-design-sweep.md`.
Working copy for measurements/citations: `/Users/lucas/eu-id/.claude/worktrees/a1-typed-mults`
on `perf/a1-typed-multiplicities`.
Deliverable: `tasks/parity/A2-report.md`. Scope: report only; no production code changes.

- [x] Gather C1-C6 constants with citations from shape dump, Q-025, perf log, source, and logs.
- [x] Run or locate the required single-thread shape dump and record the full dump in the report appendix.
- [x] Measure or locate the SHA constraint-eval span for C5; if unavailable, stop that phase and report the gap.
- [x] Apply the Phase 0 sanity gate: C3(cells) x C2 must reproduce C3(ms) within about 30%.
- [x] Compute Phase 1 current-table W sweep for W in {5, 6, 7} at blocks {1, 8, 33}.
- [x] Enumerate W=7 limb-split coupling points in `components.rs`, `constraints.rs`, and `tables.rs`.
- [x] Compute Phase 2 full-bit structured counts and projected costs using only WO formulas.
- [x] Compute Phase 3 hybrid deltas for expensive-table deletion plus bit-gadget replacement.
- [x] Write the final decision table and recommendation in `tasks/parity/A2-report.md`.
- [x] Verify every report number has a source citation or inline formula and update this review section.

## Review

- Used the clean named worktree `/Users/lucas/eu-id/.claude/worktrees/a1-typed-mults`
  on `perf/a1-typed-multiplicities`; main checkout has unrelated dirty code and an
  uncommitted `rust-toolchain.toml` change, so the report labels the toolchain caveat.
- Ran `rtk proxy env RAYON_NUM_THREADS=1 cargo test -p eu-id-prover --release shape_dump -- --ignored --nocapture`;
  it passed and the report appendix records the SHA/module/component dump.
- Ran fresh `BM_ShaZK_equiv/1/prove` and `BM_ShaZK_equiv/33/prove` Criterion filters in
  the named worktree; report uses the resulting `1031.5 ms` and `1106.1 ms` mean estimates.
- Filed and received mailbox answers for Q-031 and Q-032. Q-031 says W=6 is current and
  W=5 is invalid under the current partition bound. Q-032 says to use full-stack `~72 ns/cell`
  for full table removal and reserve Q-025's `8-15 ns/cell` for interaction-only deltas.
- C5 per-component span remains unmeasured in this checkout; the report uses Q-032's fallback
  arithmetic attribution and names that as the top risk for hybrid/full-bit projections.
- Final recommendation in `tasks/parity/A2-report.md`: spike hybrid first; current W=6 table
  floor is not the right long-term design for mobile latency.

# Faster GKR V2 Handoff

- [x] Keep eu-id production SHA path on restored full LogUp until a faster Stwo GKR design clears gates.
- [x] Write Q-028 asking Claude for a concrete patchable Stwo GKR v2 design.
- [x] Record the cross-repo boundary lesson in `tasks/lessons.md`.
- [x] Wait for `tasks/parity/mailbox/answers/Q-028.md`.
- [x] If Q-028 says "not worth local implementation", record the decision and keep GKR reverted.
- [x] Implement Q-028's required first diagnostic: an isolated PackedQM31 fraction-add microbench in `/Users/lucas/stwo`.
- [x] If the diagnostic cannot sustain the required constant, stop and keep eu-id GKR reverted.
- [x] Ask Q-029 for the next design move after the first diagnostic missed the target.
- [x] Wait for `tasks/parity/mailbox/answers/Q-029.md`.
- [x] If Q-029 kills the target, keep eu-id full LogUp and do not implement the eu-id GKR reopener.
- [x] Preserve the Stwo diagnostic bench as upstream evidence.
- [x] Implement the independent Stwo global-lift mixed-height correctness/usability fix, if locally clear.
- [x] Measure whether hand-fused PackedQM31 fraction-add materially beats the existing `Fraction` abstraction.
- [x] Ask Q-030 whether to land a production fusion slice for general Stwo consumers or stop at global-lift + diagnostic evidence.
- [x] Wait for `tasks/parity/mailbox/answers/Q-030.md`.
- [x] Record results and final disposition here.

## Review

- Opened `tasks/parity/mailbox/questions/Q-028-gkr-v2-patchable-stwo-design.md` with the Q-024/Q-025/Q-026 measurements and requested a concrete patchable design.
- Current acceptance gates remain: Stwo LogUp-GKR `<= 6 ns/term` on 1-thread 2^16 domains, eu-id feature-on SHA proving at least 3% faster than feature-off, and payload under 2.5 MB.
- Mailbox answer `tasks/parity/mailbox/answers/Q-028.md` says the eu-id upside is still capped at about 20-27 ms on a 994 ms proof, so this is justified only as Stwo infrastructure. The required first step is a microbench-only diagnostic for fused PackedQM31 fraction addition over 2^16 pairs; if that cannot sustain the needed effective multiply constant, stop before patching Stwo production code.
- Q-028's patchable sequence is: first diagnostic, then Stwo slice 1 (`fix_first_variable` in-place buffering plus fused LogUpGeneric round evaluation), then tie-back/global-lift work, then eu-id `gkr-spike` reopener for only the 17 log-16 SHA families. `maj_ch`, `range_k`, predicates, and `digest_bind` remain skipped unless later gates change that.
- Implemented `/Users/lucas/stwo/crates/stwo/benches/gkr_fraction_add.rs` and registered it in `/Users/lucas/stwo/crates/stwo/Cargo.toml`. Verification: `rtk proxy cargo fmt -p stwo --check` and `rtk proxy cargo check -p stwo --features prover --bench gkr_fraction_add` passed.
- First diagnostic result missed the Q-028 gate: fused PackedQM31 fraction-add over `2^16 * 16 = 1,048,576` scalar-lane pairs measured `11.983 ms` median, about `11.4 ns/fraction-pair` or `~3.8 ns/effective QM31 multiply`, above the `<= 1 ns/effective QM31 multiply` stop/go threshold.
- Existing Stwo full LogUpGeneric GKR baseline remains slow: `simd generic logup lookup 2^16` measured `5.8028 ms` median, about `88.5 ns/term`.
- Opened `tasks/parity/mailbox/questions/Q-029-gkr-v2-first-diagnostic-failed.md` asking whether this kills the local target or whether a lower-level packed multiplication/kernel redesign is still plausible.
- Mailbox answer `tasks/parity/mailbox/answers/Q-029.md` says the diagnostic conclusively kills the local `<= 6 ns/term` GKR-v2 target on mobile-class hardware. The fused arithmetic floor is about `38 ns/term`, still above the generous `<= 17 ns/term` break-even bound even with zero-cost tie-back.
- Disposition: eu-id SHA GKR stays full LogUp permanently for this hardware class unless a future Stwo/hardware combination independently measures through the existing reopening gates. Do not re-enable the old `gkr-spike` production path for eu-id.
- Remaining useful Stwo work is decoupled from eu-id: keep the diagnostic bench for upstream evidence, and land the global-lift Merkle mixed-height fix as a correctness/usability improvement if locally clear.
- Stwo global-lift fix implemented locally: PCS prover/verifier now use the maximum committed tree height for FRI lifting and remap query positions for every tree, not only the preprocessed tree. Added CPU/SIMD regressions where a tall first tree is followed by a shorter last tree under `lifting_log_size = None`.
- Stwo verification passed: `rtk proxy cargo fmt -p stwo --check`, `rtk proxy cargo check -p stwo --features prover`, focused `test_pcs_prove_and_verify_with_tall_non_last_tree`, broader `test_pcs_prove_and_verify`, and full `rtk proxy cargo test -p stwo --features prover` with 269 unit tests + 9 doctests passing.
- Diagnostic comparison showed hand-fused PackedQM31 fraction-add is only a small local improvement over the existing `Fraction` abstraction: at log20, existing median `13.018 ms` vs fused median `12.563 ms` for `1,048,576` pairs, about 3.5% faster. This does not change Q-029's eu-id stop decision.
- Opened `tasks/parity/mailbox/questions/Q-030-gkr-v2-after-global-lift.md` to decide whether to stop at global-lift + diagnostic evidence or still land a small production fusion slice for general Stwo consumers. As of the latest check, `tasks/parity/mailbox/answers/Q-030.md` is not present.
- Fresh Stwo verification while waiting for Q-030: `rtk proxy cargo fmt -p stwo --check`, `rtk proxy cargo check -p stwo --features prover --bench gkr_fraction_add`, focused `test_pcs_prove_and_verify_with_tall_non_last_tree`, and full `rtk proxy cargo test -p stwo --features prover` passed; full suite result was 269 unit tests and 9 doctests.
- Mailbox answer `tasks/parity/mailbox/answers/Q-030.md` chooses option 1: stop GKR-v2 production work. Keep the global-lift fix and diagnostic bench as the useful Stwo deliverables; do not implement production fusion because the measured `Fraction` vs hand-fused delta is only 3-4%, too small for a risky upstream hot-path change and irrelevant to eu-id.
- Final GKR-v2 disposition: track closed. Stwo gets one correctness/usability fix for mixed-height trees plus one diagnostic bench documenting the arithmetic floor; eu-id stays on full LogUp and keeps the existing reopener gates for future hardware/Stwo builds.

# Isolated mdoc Support

- [x] Add isolated mdoc parser tests.
- [x] Add an `eu_id_prover::mdoc` module that is not called by existing proof APIs.
- [x] Parse constrained real-shape mdoc data:
  - `IssuerSignedItemBytes` as CBOR tag 24 over `IssuerSignedItem`.
  - `MobileSecurityObject.valueDigests` for disclosed item digest checks.
  - `MobileSecurityObject.deviceKeyInfo.deviceKey` as P-256 COSE_Key.
  - COSE_Sign1 issuer signature/public payload fields.
- [x] Build an extracted host-side witness bundle for review:
  - issuer signature material,
  - MSO bytes,
  - disclosed birth date and nationality item bytes/values,
  - device key,
  - device-auth signature material over the session transcript.
- [x] Verify with focused tests and formatting.
- [x] Review diff for accidental integration into current proof flow.
- [x] Add isolated mdoc circuit profile that emits one `StarkProof` for:
  - issuer COSE_Sign1 P-256 signature,
  - device-auth P-256 signature over the session transcript,
  - SHA-256 digest checks for disclosed mdoc items,
  - age and nationality predicates bound to disclosed item bytes.
- [x] Keep the mdoc circuit API isolated under `eu_id_prover::mdoc` and do not call it from the
      current identity full-flow APIs.
- [x] Verify the isolated mdoc circuit with a focused slow release test.
- [x] Re-check parser tests, formatting, and integration leakage.

## Review

- `rtk proxy cargo test -p eu-id-prover --test mdoc_support` passed: 4 parser/host tests,
  1 slow proof test ignored by default.
- `rtk proxy cargo test -p eu-id-prover --test mdoc_support isolated_mdoc_circuit_profile_proves_and_verifies --release -- --ignored --nocapture`
  passed: isolated mdoc monolithic proof proves and verifies.
- `rtk proxy cargo test -p predicates age::strategy::tests::range_check::proves_and_verifies_with_day_and_month_borrow --release`
  passed: regression for the month-delta table bound.
- `rtk proxy cargo test -p predicates age::strategy::range_check::air::binding_tests::bound_age_balances_with_day_and_month_borrow --release`
  passed: regression for borrowed-date DOB byte binding.
- `rtk proxy cargo test -p eu-id-prover --test nonce_signature identity_with_nonce_flow_verifies --release -- --include-ignored`
  passed: existing nonce monolith regression.
- `rtk proxy cargo fmt --check` passed.
- Integration leakage check: `extract_pid_mdoc` / `MdocPidRequest` are referenced only by
  `crates/eu-id-prover/src/mdoc.rs` and `crates/eu-id-prover/tests/mdoc_support.rs`;
  the existing proof APIs do not call the new module.

# EUID mdoc Credential Format v1

Source of truth: `tasks/mdoc-credential-format-spec.md`.

- [x] Enforce ISO-correct `IssuerSignedItemBytes` as `#6.24(bstr .cbor IssuerSignedItem)`.
- [x] Keep item digest hashing over the full received tag-24 byte string.
- [x] Enforce COSE_Sign1 protected header `a1 01 26`, compact ES256 signatures, and strict P-256 ES256 COSE keys.
- [x] Parse and enforce MSO `version`, `docType`, `digestAlgorithm`, `valueDigests`, `deviceKeyInfo`, and `validityInfo`.
- [x] Add manual CBOR tdate parsing for exact `YYYY-MM-DDTHH:MM:SSZ` values without new dependencies.
- [x] Carry MSO signed / valid-from / valid-until dates on `ExtractedPidMdoc`.
- [x] In `MdocCircuitStatement::from_extracted`, reject text circuit values, offset drift, windows outside SHA-256 block 0, expired credentials, and not-yet-valid credentials.
- [x] Update isolated fixtures to the v1 profile and add knobs for malformed profile cases.
- [x] Add fast host/profile rejection tests with exact errors.
- [x] Keep the slow isolated monolithic mdoc circuit proof passing.
- [x] Add `docs/mdoc-credential-format.md` and point `docs/credential-format.md` to it.
- [x] Re-run the required verification commands and record results here.

## Review

- `rtk proxy cargo test -p eu-id-prover --test mdoc_support` passed: 17 fast tests passed, 1 slow proof test ignored by default.
- `rtk proxy cargo test -p eu-id-prover --test mdoc_support isolated_mdoc_circuit_profile_proves_and_verifies --release -- --ignored` passed: isolated mdoc monolithic proof proves and verifies under the v1 profile fixture.
- `rtk cargo clippy -p eu-id-prover` passed: 0 errors; remaining warnings are pre-existing outside the touched mdoc profile code.
- `rtk proxy cargo fmt --check` passed.
- Isolation scan: `extract_pid_mdoc`, `MdocPidRequest`, `MdocCircuitStatement`, `prove_mdoc_circuit`, and `verify_mdoc_circuit` are referenced only by `crates/eu-id-prover/src/mdoc.rs` and `crates/eu-id-prover/tests/mdoc_support.rs`; the existing identity full-flow APIs do not call the isolated mdoc module.

# EUID mdoc Profile Gap Audit

- [x] Enforce frozen PID `docType` and namespace constants, not just equality with the request.
- [x] Enforce COSE_Sign1 `unprotected` is a map for issuer and device signatures.
- [x] Enforce strict ES256 P-256 COSE_Key shape without extra fields.
- [x] Add focused rejection tests for non-profile doctype/namespace and malformed digestID.
- [x] Re-run mdoc fast tests, slow release proof, clippy, fmt, and isolation scan.

## Review

- `rtk proxy cargo test -p eu-id-prover --test mdoc_support` passed: 21 fast tests passed, 1 slow proof test ignored by default.
- `rtk proxy cargo test -p eu-id-prover --test mdoc_support isolated_mdoc_circuit_profile_proves_and_verifies --release -- --ignored` passed: isolated mdoc monolithic proof still proves and verifies.
- `rtk cargo clippy -p eu-id-prover` passed: 0 errors; remaining warnings are pre-existing outside the touched mdoc profile code.
- `rtk proxy cargo fmt --check` passed.
- Isolation scan still shows the isolated mdoc API referenced only by `crates/eu-id-prover/src/mdoc.rs` and `crates/eu-id-prover/tests/mdoc_support.rs`.

# Full mdoc Implementation Plan — Phase 0 Bench Truth

Source of truth: `tasks/mdoc-full-impl-plan.md`.

- [x] Add a reusable deterministic EUID mdoc profile-v1 fixture for benches/FFI.
- [x] Add `mdoc_bench` Criterion coverage for `prove_mdoc_circuit` / `verify_mdoc_circuit`.
- [x] Register `mdoc_bench` in `crates/eu-id-prover/Cargo.toml`.
- [x] Add `eu_id_bench_mdoc` to `crates/eu-id-ffi`.
- [x] Extend `crates/eu-id-prover/src/shape_dump.rs` with the mdoc circuit's 12-module column/cell breakdown.
- [x] Record the mdoc baseline row in `crates/eu-id-prover/benches/docs/perf-log.md`.
- [x] Run Phase 0 verification and record results.

## Review

- `rtk proxy cargo test -p eu-id-prover --test mdoc_support` passed: 21 fast tests passed, 1 slow proof test ignored by default.
- `rtk proxy cargo test -p eu-id-prover --test mdoc_support isolated_mdoc_circuit_profile_proves_and_verifies --release -- --ignored` passed.
- `rtk cargo check -p eu-id-ffi` passed.
- `rtk proxy cargo bench -p eu-id-prover --bench mdoc_bench --no-run` passed.
- `rtk proxy env RAYON_NUM_THREADS=1 cargo bench -p eu-id-prover --bench mdoc_bench` passed and produced the recorded baseline: prove 5.0325 s, verify 28.089 ms, proof 4,563,243 bytes.
- `rtk proxy cargo test -p eu-id-prover --release shape_dump -- --ignored --nocapture` passed and produced the recorded mdoc 12-module total: 16,644 columns, 79,988,576 cells.
- `rtk cargo clippy -p eu-id-prover` passed: 0 errors; remaining warnings are pre-existing outside the touched mdoc profile code.
- `rtk proxy cargo fmt --check` passed.

# Full mdoc Implementation Plan — Phase 0b SHA/P256 Sizing Waste

Source of truth: `tasks/mdoc-full-impl-plan.md`.

- [x] Check whether the four SHA modules in `prove_mdoc_circuit` can use per-instance `log_n_rows` instead of `shared_sha_log`.
- [x] Accept SHA option 1 for Phase 0b per mailbox Q-001; keep `shared_sha_log` for now.
- [x] If per-instance SHA sizing is not valid within a day, write a costed question to `tasks/mdoc-mailbox/`.
- [x] Verify whether the mdoc device P256 module can share preprocessed columns without `.with_preprocessed_namespace("mdoc/device")`.
- [x] Accept P256 option 1 for Phase 0b per mailbox Q-001; keep the `mdoc/device` namespace for witness-dependent hinted-mul schedules.
- [x] Add the combined-proof preprocessed-ID/content invariant guard.
- [x] Measure SHA/P256 accepted waste and apply the Q-001 `< 1.0M cells` decision rule.
- [x] Record the Phase 0b perf delta vs Phase 0 baseline in `crates/eu-id-prover/benches/docs/perf-log.md`.
- [x] Run Phase 0b verification and record results.

## Review

- Per-instance SHA log sizing was tested and rejected for now: the slow mdoc proof failed with `Prove("ConstraintsNotSatisfied")`.
- Dropping the mdoc device P256 namespace was tested and rejected for now: the slow mdoc proof failed with `Prove("ConstraintsNotSatisfied")`.
- Restored the known-good `shared_sha_log` path and re-ran `rtk proxy cargo test -p eu-id-prover --test mdoc_support isolated_mdoc_circuit_profile_proves_and_verifies --release -- --ignored`; it passed.
- Restored the known-good `mdoc/device` P256 namespace and re-ran the same slow proof; it passed.
- Updated the costed design question at `tasks/mdoc-mailbox/questions/Q-001-phase0b-sizing-waste-route.md`.
- Re-checked after normalizing the mailbox path: `rtk proxy cargo test -p eu-id-prover --test mdoc_support isolated_mdoc_circuit_profile_proves_and_verifies --release -- --ignored` and `rtk proxy cargo fmt --check` passed.
- Mailbox answer `tasks/mdoc-mailbox/answers/Q-001.md` chose SHA option 1 + P256 option 1 for Phase 0b after adding the guard and pricing the waste; larger SHA/P256 ID refactors are separate follow-up scope, not gates on Phase A.
- Added a generic `air-core::prove` invariant guard: every composed proof fingerprints preprocessed columns before first-writer-wins tree-0 dedup and panics if equal IDs map to unequal content, naming both modules and the ID.
- `rtk proxy cargo test -p air-core preprocessed_invariant -- --nocapture` passed: duplicate equal content accepted; duplicate unequal content rejected with the module names and ID.
- Phase 0b accepted waste is 529,792 cells: SHA issuer 0, device 216,960, birth-date 156,928, nationality 155,904; P256 namespaced content-identical preprocessed duplication 0. This is below the 1,000,000-cell Q-001 threshold.
- `rtk proxy cargo test -p eu-id-prover --test mdoc_support phase0b_sizing_waste_stays_below_refactor_threshold -- --nocapture` passed.
- `rtk proxy cargo test -p eu-id-prover --test mdoc_support` passed: 22 fast tests passed, 1 slow proof test ignored by default.
- `rtk proxy cargo test -p eu-id-prover --test mdoc_support isolated_mdoc_circuit_profile_proves_and_verifies --release -- --ignored` passed.
- `rtk proxy cargo test -p eu-id-prover --release shape_dump -- --ignored --nocapture` passed and printed the Phase 0b waste breakdown.
- `rtk proxy env RAYON_NUM_THREADS=1 cargo bench -p eu-id-prover --bench mdoc_bench` passed: mdoc/prove 5.0498 s, mdoc/verify 27.798 ms, proof 4,563,243 bytes; Criterion reported no performance change.

# GKR Tie-Back Item 3 Contract — Phase 0

Source of truth: `/Users/lucas/stwo/tasks/gkr-item3-contract.md`.

- [x] Add the temporary local Stwo `[patch."https://github.com/0xLucqs/stwo.git"]`
      override at the end of workspace `Cargo.toml`, without editing workspace dependency revs.
- [x] Verify `cargo check -p stwo-sha256 --features gkr-spike` against the local
      `/private/tmp/stwo-dev-copy` fork.
- [x] Remove the diagnostic `#[ignore]` from
      `vendored_mle_eval_component_proves_and_verifies_with_pad_column`.
- [x] Verify `cargo test -p stwo-sha256 --features gkr-spike` so all spike tests,
      including the pad-column regression, pass.
- [x] If the pad-column spike test passes, record Q-005/Q-006 closure and the
      sound xor_8 tie-back milestone in `tasks/parity/WO-S1-gkr-spike.md`.
- [x] Run `make test` for full-workspace regression coverage.
- [x] Only after Phase 0 is green, begin Phase 1 discovery for production xor_8
      wiring behind `gkr-spike`, preserving the transcript order required by the contract.

## Review

- Added the temporary local Stwo patch override to workspace `Cargo.toml`; this is
  explicitly local and must not be committed.
- `rtk proxy cargo check -p stwo-sha256 --features gkr-spike` initially exposed
  a Stwo fork API drift: `SimdDomainEvaluator::new` now takes `n_fracs`.
- Patched the vendored SHA MLE-eval quotient call to pass `0`, matching the local
  fork's example MLE-eval component, then `cargo check` passed.
- Removed the diagnostic ignore from
  `vendored_mle_eval_component_proves_and_verifies_with_pad_column`.
- `rtk proxy cargo test -p stwo-sha256 --features gkr-spike` failed and Phase 0
  is halted per contract. Exact failure: the pad-column regression aborts at
  `/private/tmp/stwo-dev-copy/crates/constraint-framework/src/prover/simd_domain.rs:91:50`
  with `unsafe precondition(s) violated: slice::get_unchecked requires that the index is within the slice`
  and exits with `SIGABRT`.
- Continued Phase 0 debugging after the resume request. Root cause was that the local
  Stwo dev-copy still rejected or mis-remapped active commitment trees taller than the
  FRI lifting height; patched `/private/tmp/stwo-dev-copy` to use the generalized
  shorter-or-taller query-position remap in prover and verifier.
- Refactored the pad-column diagnostic so the MLE component keeps its natural degree
  and a dedicated zero-constraint pad component owns the extra tree-2 pad column.
- `rtk proxy cargo check -p stwo-sha256 --features gkr-spike` passed.
- `rtk proxy cargo test -p stwo-sha256 --features gkr-spike` passed: 126 lib tests
  passed, 2 ignored; integration/structural targets passed with their expected ignored
  slow tests.
- Recorded the Q-005/Q-006 closure and Item 3 Phase 0 update in
  `tasks/parity/WO-S1-gkr-spike.md`.
- `rtk proxy make test` passed: full workspace `cargo test --workspace --release` completed
  with the expected ignored slow/diagnostic tests.

# GKR Tie-Back Item 3 Contract — Phase 1 xor_8

Source of truth: `/Users/lucas/stwo/tasks/gkr-item3-contract.md`.

- [x] Locate the shared `air-core` proof composition order and record it in the WO log.
- [x] Confirm the production `xor_8` GKR tie-back is wired behind `gkr-spike` in
      `crates/stwo-sha256/src/air.rs`.
- [x] Add a downstream transcript digest-boundary test for the current single-table
      `xor_8` GKR tie-back path.
- [x] Verify the focused digest-boundary test with `gkr-spike`.
- [x] Verify the `stwo-sha256` package with `gkr-spike`.
- [x] Verify the `stwo-sha256` package without `gkr-spike`.
- [x] Verify the standalone SHA release proof with `gkr-spike`.
- [x] Re-check the identity e2e acceptance gate with and without `gkr-spike`.
- [x] Record a fresh Item 3 perf row, or explicitly carry forward the existing WO-S1
      `xor_8` row if the single-table implementation is unchanged.
- [ ] Resolve the identity e2e acceptance blocker or get explicit approval to exclude
      the pre-existing P256 preprocessed-column invariant from this contract gate.
- [ ] Start Phase 2 family batching only after the Phase 1 acceptance decision is clear.

## Review

- Current transcript order in `air-core::prove`: mix PCS config, commit tree 0
  preprocessed columns, mix public statement, commit tree 1 witness/multiplicity columns,
  draw relations, write tree 2 interaction columns, mix claimed sums, commit tree 2,
  run post-interaction GKR proof messages, commit post-interaction tie-back tree, then
  build components and call Stwo `prove`.
- `crates/stwo-sha256/src/air.rs` already wires the current table-side `xor_8` GKR path:
  `prove_post_interaction` calls `prove_xor_8_gkr`, checks the producer claimed sum and
  verifier-derived denominator claim, stores the wire proof/artifact, and
  `write_post_interaction` commits the MLE tie-back trace plus pad column.
- Added
  `air::gkr_transcript_digest_tests::xor_8_gkr_transcript_digest_boundaries_match`.
  It manually drives the same production phase order through the post-interaction tree
  and asserts prover/verifier channel digests match after tree 2, after the `xor_8` GKR
  proof is transcript-bound, and after the tie-back commitment.
- `rtk proxy cargo test -p stwo-sha256 --features gkr-spike xor_8_gkr_transcript_digest_boundaries_match -- --ignored --nocapture`
  passed.
- `rtk proxy cargo test -p stwo-sha256 --features gkr-spike` passed: 126 passed,
  3 ignored in the lib target; integration and doctest targets passed.
- `rtk proxy cargo test -p stwo-sha256` passed: 121 passed, 1 ignored in the lib target;
  integration and doctest targets passed.
- `rtk proxy cargo test -p stwo-sha256 --features gkr-spike --release prove_and_verify_abc -- --exact --ignored --nocapture`
  passed.
- `rtk proxy cargo test -p eu-id-prover --features gkr-spike --release prove_identity_then_verify_identity_round_trips -- --exact --ignored --nocapture`
  failed before SHA/GKR at `crates/air-core/src/lib.rs:164:21`:
  preprocessed column id `hinted_mul_schedule_active_13` has different content in two
  `stwo_p256::P256Prover` modules.
- `rtk proxy cargo test -p eu-id-prover --release prove_identity_then_verify_identity_round_trips -- --exact --ignored --nocapture`
  failed with the same P256 preprocessed-column invariant, proving this is not a
  `gkr-spike` regression. The Item 3 contract says not to touch P256, so this remains
  an acceptance blocker unless explicitly waived or moved to separate P256 scope.
- The current digest-boundary test covers the single-table `xor_8` Phase 1 order. The
  full contract's `gamma` boundary is still Phase 2 work because the current single-table
  path does not yet implement family claim batching or gamma accumulation.
- Recorded fresh current-worktree perf rows in
  `crates/eu-id-prover/benches/docs/perf-log.md`: prove 1.0046 s -> 1.2835 s,
  verify 846.76 us -> 880.82 us, composed cells 37,500,240 -> 37,238,096,
  SHA interaction cells 5,800,640 -> 5,538,496, SHA STARK bytes 60,045 -> 58,897,
  `xor_8` GKR wire bytes 0 -> 9,992, and combined STARK+GKR payload 60,045 -> 68,889.
- Fixed `shape_dump` under `gkr-spike` to mirror the post-interaction phase before
  component assembly; without that, the diagnostic panicked because the SHA MLE tie-back
  component needs the GKR artifact produced by `prove_post_interaction`.

# GKR Tie-Back Item 3 Contract — Phase 2 family batching

Source of truth: `/Users/lucas/stwo/tasks/gkr-item3-contract.md`.

- [x] Map the SHA family order from `crates/stwo-sha256/src/components.rs`.
- [x] Add a first multi-table `prove_batch` helper for the sigma-decode family
      under `gkr-spike`.
- [x] Add tests proving all eight sigma-decode tables are batched together, claim-aligned
      with the production interaction claims, and rejected on output-claim tamper.
- [x] Add gamma claim mixing/accumulation for the sigma-decode multiplicity claims.
- [x] Add one accumulated sigma-decode tie-back
      component.
- [x] Extend the digest-boundary regression to include the required
      after-claims-mixed and after-gamma boundaries.
- [x] Wire sigma-decode family batching into the production post-interaction proof path.
- [x] Add a first multi-table `prove_batch` helper for the split-pack family
      under `gkr-spike`.
- [x] Add focused split-pack helper tests for output claim alignment, tamper rejection,
      and gamma accumulation.
- [x] Convert sigma-decode, split-pack, and `maj_ch` from duplicate tie-back proofing
      to actual table conversion by skipping their old producer LogUp interaction
      columns and AIR relation emissions under `gkr-spike`.
- [x] Wire the split-pack family into the production post-interaction proof path.
- [x] Add and wire the packed `maj_ch` family as two GKR instances with one
      accumulated tie-back component.
- [ ] Finish remaining SHA scope: `range_k`, and decide whether `xor_8` must be folded
      into a final unified multi-family batch beyond its current converted single-table path.
- [ ] Confirm `digest_bind`'s terminal `range_16` emission site before converting it.
- [ ] Add predicate-family batching after SHA families.

## Review

- Added `prove_sigma_decode_gkr` / `verify_sigma_decode_gkr` in
  `crates/stwo-sha256/src/gkr_spike.rs`, using one `prove_batch` over the canonical
  `DECODE_TABLES` order.
- Added `sigma_decode_gkr_batches_all_eight_tables`: it verifies the batched proof,
  checks each GKR output claim equals the corresponding production `interaction_claim.decode[i]`,
  checks each numerator artifact claim against the matching multiplicity MLE, and checks each
  denominator artifact claim against the fixed decode-table denominator MLE.
- Added `sigma_decode_gkr_rejects_output_claim_tamper`.
- Added `mix_gkr_artifact_claims`, `draw_gkr_claim_batch_gamma`,
  `sigma_decode_accumulated_multiplicity_claim`, and
  `sigma_decode_accumulated_multiplicity_mle`.
- Added `sigma_decode_gamma_accumulator_matches_accumulated_mle`: it mixes all
  sigma-decode artifact claims before drawing `gamma`, asserts prover/verifier transcript
  digests match before/after gamma, and checks the gamma-accumulated claim equals the
  accumulated multiplicity MLE at the shared GKR point.
- `rtk proxy cargo test -p stwo-sha256 --features gkr-spike sigma_decode_gkr -- --nocapture`
  passed.
- `rtk proxy cargo test -p stwo-sha256 --features gkr-spike sigma_decode -- --nocapture`
  passed.
- `rtk proxy cargo test -p stwo-sha256 --features gkr-spike` passed: 129 lib tests
  passed, 3 ignored; integration and doctest targets passed.
- `rtk proxy cargo fmt --check` passed.
- Sigma-decode production wiring checkpoint:
  - `rtk proxy cargo check -p eu-id-prover --features gkr-spike` passed.
  - `rtk proxy cargo test -p stwo-sha256 --features gkr-spike xor_8_gkr_transcript_digest_boundaries_match -- --ignored --nocapture`
    passed and now includes after sigma-decode claims-mixed and after-gamma transcript snapshots.
  - `rtk proxy cargo test -p eu-id-prover --features gkr-spike --release shape_dump -- --ignored --nocapture`
    passed: SHA STARK proof bytes 63,233, `xor_8` GKR wire bytes 9,992,
    sigma-decode GKR wire bytes 18,392, composed cells 37,238,096.
  - `rtk proxy cargo test -p stwo-sha256 --features gkr-spike` passed: 129 lib tests
    passed, 3 ignored; integration and doctest targets passed.
  - `rtk proxy cargo test -p stwo-sha256 --features gkr-spike --release prove_and_verify_abc -- --exact --ignored --nocapture`
    passed.
  - `rtk proxy env RAYON_NUM_THREADS=1 cargo bench -p eu-id-prover --features gkr-spike --bench longfellow_equiv_bench -- BM_ShaZK_equiv/1`
    passed: `BM_ShaZK_equiv/1/prove` 1.3491 s, verify 1.1752 ms.
- Added `prove_split_pack_gkr` / `verify_split_pack_gkr` in
  `crates/stwo-sha256/src/gkr_spike.rs`, batching the four round split-pack
  tables followed by the four sigma split-pack tables in production component order.
- `rtk proxy cargo test -p stwo-sha256 --features gkr-spike split_pack -- --nocapture`
  passed: 8 tests matched, including the 3 new GKR helper tests.
- Superseded caveat: sigma-decode was initially production transcript-bound and MLE-tied
  but still a duplicate side proof. The later actual-conversion checkpoint below removes
  the old producer LogUp interaction columns under `gkr-spike`.
- Split-pack production wiring checkpoint:
  - `rtk proxy cargo check -p stwo-sha256 --features gkr-spike` passed.
  - `rtk proxy cargo check -p eu-id-prover --features gkr-spike` passed.
  - `rtk proxy cargo test -p stwo-sha256 --features gkr-spike xor_8_gkr_transcript_digest_boundaries_match -- --ignored --nocapture`
    passed and now includes split-pack claims-mixed and gamma transcript snapshots.
  - `rtk proxy cargo test -p stwo-sha256 --features gkr-spike --release prove_and_verify_abc -- --exact --ignored --nocapture`
    passed.
  - `rtk proxy cargo test -p stwo-sha256 --features gkr-spike` passed: 132 lib tests
    passed, 3 ignored; integration and doctest targets passed.
  - `rtk proxy cargo test -p eu-id-prover --features gkr-spike --release shape_dump -- --ignored --nocapture`
    passed: SHA STARK proof bytes 63,713, `xor_8` GKR wire bytes 9,992,
    sigma-decode GKR wire bytes 18,392, split-pack GKR wire bytes 18,392,
    composed cells 37,238,096.
  - `rtk proxy env RAYON_NUM_THREADS=1 cargo bench -p eu-id-prover --features gkr-spike --bench longfellow_equiv_bench -- BM_ShaZK_equiv/1`
    passed: `BM_ShaZK_equiv/1/prove` 1.4686 s, verify 1.5943 ms.
  - `rtk proxy cargo fmt --check` passed.
- Superseded caveat: split-pack was initially production transcript-bound and MLE-tied
  but still additive. The later actual-conversion checkpoint below removes the old
  producer LogUp interaction columns under `gkr-spike`.
- `maj_ch` production wiring checkpoint:
  - `rtk proxy cargo test -p stwo-sha256 --features gkr-spike maj_ch -- --nocapture`
    passed: 5 tests matched, including the 3 new GKR helper tests.
  - `rtk proxy cargo check -p stwo-sha256 --features gkr-spike` passed.
  - `rtk proxy cargo check -p eu-id-prover --features gkr-spike` passed.
  - `rtk proxy cargo test -p stwo-sha256 --features gkr-spike xor_8_gkr_transcript_digest_boundaries_match -- --ignored --nocapture`
    passed and now includes `maj_ch` claims-mixed and gamma transcript snapshots.
  - `rtk proxy cargo test -p stwo-sha256 --features gkr-spike --release prove_and_verify_abc -- --exact --ignored --nocapture`
    passed.
  - `rtk proxy cargo test -p stwo-sha256 --features gkr-spike` passed: 135 lib tests
    passed, 3 ignored; integration and doctest targets passed.
  - `rtk proxy cargo test -p eu-id-prover --features gkr-spike --release shape_dump -- --ignored --nocapture`
    passed: SHA STARK proof bytes 64,193, `xor_8` GKR wire bytes 9,992,
    sigma-decode GKR wire bytes 18,392, split-pack GKR wire bytes 18,392,
    `maj_ch` GKR wire bytes 13,872, composed cells 37,238,096.
  - `rtk proxy env RAYON_NUM_THREADS=1 cargo bench -p eu-id-prover --features gkr-spike --bench longfellow_equiv_bench -- BM_ShaZK_equiv/1`
    passed: `BM_ShaZK_equiv/1/prove` 1.6705 s, verify 1.7869 ms.
  - `rtk proxy cargo fmt --check` passed.
- Superseded caveat: `maj_ch` was initially additive production side-proof work. The
  later actual-conversion checkpoint below removes its old producer LogUp interaction column
  under `gkr-spike`.
- Actual conversion checkpoint for sigma-decode, split-pack, and `maj_ch`:
  - Under `gkr-spike`, their producer-side LogUp interaction traces are still computed for
    claimed sums/GKR output checks, but no longer committed into the interaction tree.
  - Their AIR producer components still read preprocessed and multiplicity columns, but no
    longer emit duplicate `add_to_relation` constraints under `gkr-spike`.
  - `rtk proxy cargo check -p stwo-sha256 --features gkr-spike` passed.
  - `rtk proxy cargo check -p eu-id-prover --features gkr-spike` passed.
  - `rtk proxy cargo test -p stwo-sha256 --features gkr-spike xor_8_gkr_transcript_digest_boundaries_match -- --ignored --nocapture`
    passed.
  - `rtk proxy cargo test -p stwo-sha256 --features gkr-spike --release prove_and_verify_abc -- --exact --ignored --nocapture`
    passed.
  - `rtk proxy cargo test -p stwo-sha256 --features gkr-spike` passed: 135 lib tests
    passed, 3 ignored; integration and doctest targets passed.
  - `rtk proxy cargo test -p eu-id-prover --features gkr-spike --release shape_dump -- --ignored --nocapture`
    passed: SHA STARK proof bytes 58,561, `xor_8` GKR wire bytes 9,992,
    sigma-decode GKR wire bytes 18,392, split-pack GKR wire bytes 18,392,
    `maj_ch` GKR wire bytes 13,872, composed cells 31,995,216, and SHA interaction
    cells 295,616.
  - `rtk proxy env RAYON_NUM_THREADS=1 cargo bench -p eu-id-prover --features gkr-spike --bench longfellow_equiv_bench -- BM_ShaZK_equiv/1`
    passed: `BM_ShaZK_equiv/1/prove` median 1.2735 s, verify median 1.7339 ms.
  - Net cumulative cells versus feature-off baseline: composed committed cells
    37,500,240 -> 31,995,216; SHA interaction cells 5,800,640 -> 295,616.
  - Remaining contract caveat: the current implementation still uses separate family GKR
    proof calls rather than one unified multi-family `prove_batch` call.
  - WO-S4 reconciliation: `tasks/parity/WO-S4-gkr-tieback-production.md` is now the active
    payoff gate for this track. `range_k` is not production-converted; the current production
    SHA proof path contains no `range_k_gkr` wiring. Per WO-S4 P-1/P-2, `range_k` must stay
    skipped unless a filled net-cells formula shows at least 2x tie-back overhead payoff.
  - Revert fix: after removing stale `range_k` GKR transport and post-interaction blocks,
    `interaction_trace_log_sizes()` still skipped the four ordinary range producer columns
    under `gkr-spike`. That made Stwo open 228 tree-2 columns while the verifier layout
    declared 212. Restored range interaction-size accounting unconditionally; range remains on
    ordinary LogUp and is not GKR-converted.
  - Re-verification after WO-S4 reconciliation:
    `rtk proxy cargo fmt --check` passed;
    `rtk proxy cargo check -p stwo-sha256 --features gkr-spike` passed;
    `rtk proxy cargo check -p eu-id-prover --features gkr-spike` passed;
    `rtk proxy cargo test -p stwo-sha256 --features gkr-spike --release prove_and_verify_abc -- --exact --ignored --nocapture` passed;
    `rtk proxy cargo test -p stwo-sha256 --features gkr-spike xor_8_gkr_transcript_digest_boundaries_match -- --ignored --nocapture` passed;
    `rtk proxy cargo test -p eu-id-prover --features gkr-spike --release shape_dump -- --ignored --nocapture` passed and printed no range_k GKR proof bytes;
    `rtk proxy cargo test -p stwo-sha256 --features gkr-spike` passed: 138 lib tests,
    11 constraint-negative tests, 2 structural tests, 3 ignored lib tests, 10 ignored slow
    prove/verify tests, and 2 ignored doctests.
  - Unified converted-SHA batch checkpoint:
    - Folded converted SHA table families into one production `prove_batch` with 19 instances:
      `xor_8`, 8 sigma-decode outputs, 8 split-pack outputs, and `maj_ch`/`ch`.
    - Kept per-family accumulated tie-back components and gammas; no same-height cross-family
      tie-back merge has been shipped yet.
    - Kept `range_k` skipped under WO-S4 P-1/P-2; the production path still contains no
      `range_k_gkr` transport or verifier wiring.
    - Verification passed:
      `rtk proxy cargo fmt -p stwo-sha256 --check`;
      `rtk proxy rustfmt --edition 2021 --check crates/eu-id-prover/src/lib.rs crates/eu-id-prover/src/shape_dump.rs crates/eu-id-prover/benches/common/stages.rs`;
      `rtk proxy cargo check -p stwo-sha256 --features gkr-spike`;
      `rtk proxy cargo check -p eu-id-prover --features gkr-spike`;
      `rtk proxy cargo test -p stwo-sha256 --features gkr-spike xor_8_gkr_transcript_digest_boundaries_match -- --ignored --nocapture`;
      `rtk proxy cargo test -p stwo-sha256 --features gkr-spike --release prove_and_verify_abc -- --exact --ignored --nocapture`;
      `rtk proxy cargo test -p stwo-sha256 --features gkr-spike`;
      `rtk proxy cargo test -p eu-id-prover --features gkr-spike --release shape_dump -- --ignored --nocapture`;
      `rtk proxy env RAYON_NUM_THREADS=1 cargo bench -p eu-id-prover --features gkr-spike --bench longfellow_equiv_bench -- BM_ShaZK_equiv/1`.
    - Measured shape/bench after unified batch: SHA standalone STARK proof bytes 57,489;
      unified converted-SHA GKR proof bytes 34,272; SHA STARK+GKR payload 91,761 bytes;
      composed committed cells 31,995,216; SHA interaction cells 295,616;
      `BM_ShaZK_equiv/1/prove` median 1.5040 s; verify median 1.5584 ms.
  - P-3 same-height 2^16 tie-back merge checkpoint:
    - Merged `xor_8`, sigma-decode, and split-pack into one log-16 MLE tie-back component using
      one post-GKR Fiat-Shamir challenge. `maj_ch` remains separate at its larger table height.
    - Extended the digest-boundary regression to record the new log-16 tie-back gamma boundary.
    - Added explicit post-interaction tree accounting to `shape_dump`.
    - Verification passed:
      `rtk proxy cargo check -p stwo-sha256 --features gkr-spike`;
      `rtk proxy cargo check -p eu-id-prover --features gkr-spike`;
      `rtk proxy cargo test -p stwo-sha256 --features gkr-spike xor_8_gkr_transcript_digest_boundaries_match -- --ignored --nocapture`;
      `rtk proxy cargo test -p stwo-sha256 --features gkr-spike --release prove_and_verify_abc -- --exact --ignored --nocapture`;
      `rtk proxy cargo test -p eu-id-prover --features gkr-spike --release shape_dump -- --ignored --nocapture`;
      `rtk proxy cargo test -p stwo-sha256 --features gkr-spike`;
      `rtk proxy env RAYON_NUM_THREADS=1 cargo bench -p eu-id-prover --features gkr-spike --bench longfellow_equiv_bench -- BM_ShaZK_equiv/1`.
    - Measured P-3 result versus the unified-batch checkpoint: SHA post-interaction tree
      33 cols / 4,194,304 cells -> 17 cols / 3,145,728 cells; `GRAND+POST` cells
      36,189,520 -> 35,140,944; SHA standalone STARK proof bytes 57,489 -> 58,961;
      converted-SHA GKR proof bytes unchanged at 34,272; SHA STARK+GKR payload
      91,761 -> 93,233 bytes; `BM_ShaZK_equiv/1/prove` median 1.2311 s and verify median
      1.2466 ms.
    - Decision: keep P-3 merge. It saves 1,048,576 committed post-interaction cells and improves
      measured verify time; the 1,472-byte SHA payload increase remains well below the 2.5 MB
      mobile ceiling.
  - Predicate P-1 gate:
    - Age range-check strategy table-side conversion is a measured no-go for the default identity
      shape. Cells removed would be 13,936 (`calendar` 12,288, `valid_day` 768, `day_delta` 160,
      `month_delta` 80, `year_delta` 640) before tie-back, while one MLE tie-back per table costs
      18,816 cells (`calendar` 16,384, `valid_day` 1,024, `day_delta` 256, `month_delta` 128,
      `year_delta` 1,024), for net -4,880 cells before GKR wire/verify cost.
    - Age bit-decomposition's table-side subset is also a no-go: `calendar` + `valid_day` remove
      13,056 cells and add 17,408 tie-back cells, net -4,352 before GKR wire/verify cost.
    - Nationality table conversion is a no-go: it removes 80 cells and adds 128 tie-back cells,
      net -48 before GKR wire/verify cost.
    - Decision: skip predicate GKR conversion under WO-S4 P-1/P-4. The predicate tables stay on
      ordinary LogUp; this is the production implementation decision, not a missing circuit.
  - `digest_bind` scope decision:
    - Confirmed the terminal SHA `range_16` emission site:
      `crates/stwo-sha256/src/constraints.rs` wires `RangeKind::Range16` over final-block
      `h_out` limbs on `t = 63`, then constrains the 32 digest byte-view columns and yields those
      bytes on the shared digest relation when `expose_digest` is set. The interaction mirror is
      `crates/stwo-sha256/src/interaction.rs` in the finalization/digest-yield block.
    - Confirmed the bridge side:
      `crates/stwo-p256/src/components/digest_bind/air.rs` consumes the shared digest relation and
      locally range-checks digest bytes/carries through namespaced range8/range13 providers in
      `crates/stwo-p256/src/components/digest_bind/module.rs`.
    - There is no standalone fixed "digest table" to convert; the digest equality itself is a
      cross-module LogUp relation, not a verifier-evaluable fixed table.
    - Candidate fixed-table conversions are P-1 no-go:
      digest_bind range8 removes 1,280 cells and adds 2,048 tie-back cells, net -768 before wire;
      digest_bind range13 removes 40,960 cells and adds 65,536 tie-back cells, net -24,576 before
      wire; SHA `range_16` remains covered by the earlier WO-S4 `range_k` skip.
    - Decision: skip `digest_bind` GKR conversion under WO-S4 P-1/P-4. The existing digest relation
      binding remains the credible proof mechanism; adding a GKR side proof here would increase
      cells/wire/verify.
  - Item 3 scoped implementation status: SHA converted tables and P-3 merge are implemented;
    predicates and `digest_bind` are closed by documented P-1/P-4 skips; `range_k` stays skipped;
    P256 lookups stayed out of scope.
  - Final scoped verification:
    - `rtk proxy cargo test -p stwo-sha256` passed without `gkr-spike`.
    - `rtk proxy cargo test -p stwo-sha256 --features gkr-spike` passed.
    - `rtk proxy cargo check -p eu-id-prover` passed without `gkr-spike`.
    - `rtk proxy cargo check -p eu-id-prover --features gkr-spike` passed.
    - `rtk proxy cargo clippy -p stwo-sha256 --features gkr-spike -- -D warnings` passed after
      SHA-local clippy cleanup.
    - `rtk proxy make test` passed (`cargo test --workspace --release`).
    - `rtk proxy make check` still fails only in out-of-scope
      `crates/stwo-p256/src/components/*` clippy lints (`final_check`, `hinted_mul`). WO-S4 says
      not to touch P256 components for this item, so this is recorded as an external verification
      caveat rather than fixed in Item 3.
  - 2026-07-04 design verdict request:
    - Lucas flagged the current performance trade as likely bad design: the P-3 merged SHA GKR path
      saves cells but still regresses 1-block SHA prove time versus the feature-off baseline
      (`1.0046 s -> 1.2311 s`) and increases SHA payload (`60,045 -> 93,233` bytes).
    - Sent `tasks/parity/mailbox/questions/Q-024-wo-s4-gkr-design-verdict.md` asking Claude/Fable
      whether to keep, revert, redesign, or stop the production GKR tie-back path before expanding
      or optimizing it further.
    - Fresh checks before filing Q-024: `rtk proxy cargo test -p stwo-sha256 --features gkr-spike`
      passed; `rtk proxy cargo test -p stwo-sha256 --features gkr-spike
      xor_8_gkr_transcript_digest_boundaries_match -- --ignored --nocapture` passed.
    - Latest mailbox poll: no `tasks/parity/mailbox/answers/Q-024.md` exists yet; content search in
      `tasks/parity/mailbox/answers/` found no WO-S4/GKR design answer. Further production GKR work
      remains paused pending that decision.
    - Q-024 answered by Fable on 2026-07-04:
      - Metric of record is single-thread SHA prove wall time, with proof bytes as secondary ceiling.
      - Current production GKR path is measured net-negative: `-2.36M` committed cells but `+226 ms`
        SHA prove time, so committed cells are rejected as the controlling proxy.
      - Decision: revert production path back to full LogUp tables; keep all GKR machinery/tests
        feature-gated under `gkr-spike`.
      - Do not chase local GKR variants. Reopen only if upstream Stwo GKR gets ~5x faster/parallel
        or if a separate architect-scoped content-aware table redesign lands.
      - Next implementation task: remove `gkr-spike` production-default effect, restore feature-off
        production baseline, rerun SHA benches feature-off, and log the restore rows.
    - Q-025 answered by Fable on 2026-07-04:
      - Root cause is converting cheap marginal SHA interaction cells (~8-15 ns/cell) into
        expensive serial GKR terms (~80 ns/term) plus a 3.1M-cell tie-back tree.
      - Exact current SHA mix is ~3.28M GKR terms, predicting ~262 ms GKR cost and ~242 ms net
        slowdown, close to the measured +226 ms.
      - Diagnostic instruction: one timer around unified `prove_batch` if needed, then stop; proceed
        with Q-024 revert unchanged.
    - Sent `tasks/parity/mailbox/questions/Q-026-gkr-design-for-15ns-target.md` asking for a future
      GKR design study that could hit the target constant (Lucas named 15 ns/cell; question asks
      Fable to clarify whether the right unit is ns/GKR term or effective ns/removed committed cell).
      This does not block the Q-024 revert.
    - User follow-up: once Q-026/better-GKR design is found, copy the resulting design into
      `/Users/lucas/stwo/better-gkr.md` for the Stwo repo.
    - Q-026 answered by Fable on 2026-07-04 and copied to `/Users/lucas/stwo/better-gkr.md`:
      - Correct unit is ns/GKR term, not ns/cell.
      - Current 3.1M-cell tie-back needs ~6 ns/term to break even; with tie-back shrunk to its
        floor, ~15-17 ns/term is enough.
      - Best realistic design drops `maj/ch`, converts only the 17 log-16 instances, targets
        ~5 ns/term via upstream SIMD/streaming LogUp GKR, and shrinks tie-back to one shared log-16
        MLE-eval pair (~0.3M cells), for an expected 20-25 ms SHA prove win.
      - Disposition remains no local prototype; file upstream Stwo request for "GKR v2:
        SIMD/streaming LogUp fold, target <=6 ns/term 1-thread, first-class MLE tie-back component,
        per-tree lift compatible with mixed-size trees."
  - Repo-local Q-024 revert implementation plan:
    - [x] Remove production GKR proof transport from `stwo-sha256`/`eu-id-prover` proof objects.
    - [x] Keep `crates/stwo-sha256/src/gkr_spike.rs` helpers/tests under `gkr-spike`.
    - [x] Ensure `gkr-spike` no longer changes production SHA proof layout: full LogUp interaction
      tables stay committed; no production post-interaction GKR tie-back tree.
    - [x] Restore/record feature-off SHA baseline rows after the revert.
      - Shape dump with `gkr-spike` after revert: SHA proof bytes `60,045`; SHA interaction cells
        `5,800,640`; composed cells `37,500,240`; no converted SHA GKR proof bytes; no post tree.
      - Perf log now records Q-024 revert rows and Q-026 upstream reopening gate.
    - [x] Verify feature-off and feature-on compile/test paths; feature-on should keep spike tests
      without changing production proof transport.
      - `rtk proxy cargo check -p stwo-sha256 --features gkr-spike` passed.
      - `rtk proxy cargo check -p eu-id-prover --features gkr-spike` passed.
      - `rtk proxy cargo test -p eu-id-prover --features gkr-spike --release shape_dump -- --ignored --nocapture`
        passed and restored full LogUp SHA shape.
      - `rtk proxy cargo test -p stwo-sha256 --features gkr-spike` passed.
      - `rtk proxy cargo test -p stwo-sha256 --features gkr-spike
        xor_8_gkr_transcript_digest_boundaries_match -- --ignored --nocapture` passed with the new
        no-production-tieback invariant.
      - `rtk proxy cargo test -p stwo-sha256 --features gkr-spike --release prove_and_verify_abc
        -- --exact --ignored --nocapture` passed.
      - `rtk proxy cargo check -p stwo-sha256` passed.
      - `rtk proxy cargo check -p eu-id-prover` passed.
      - `rtk proxy cargo test -p stwo-sha256` passed.
      - `rtk proxy cargo fmt -p stwo-sha256 --check` passed.
      - `rtk proxy rustfmt --edition 2021 --check crates/eu-id-prover/src/lib.rs
        crates/eu-id-prover/src/shape_dump.rs crates/eu-id-prover/benches/common/stages.rs`
        passed.
      - `rtk proxy cargo test -p eu-id-prover` passed.
      - `rtk proxy cargo test -p eu-id-prover --features gkr-spike` passed.
      - `rtk proxy cargo clippy -p stwo-sha256 --features gkr-spike -- -D warnings` passed.
      - `rtk proxy make test` passed.
      - `rtk proxy env RAYON_NUM_THREADS=1 cargo bench -p eu-id-prover --bench
        longfellow_equiv_bench -- BM_ShaZK_equiv/1` passed: prove median `993.73 ms`, verify
        median `608.68 us`; perf log updated.
      - `rtk proxy make check` still fails only in pre-existing out-of-scope
        `crates/stwo-p256/src/components/*` clippy lints (`final_check`, `hinted_mul`). The Q-024
        revert did not touch P256 components.
