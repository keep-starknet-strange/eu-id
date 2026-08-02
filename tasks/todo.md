# TS13 public-input-unlinkable identity demo

Branch: `codex/ts13-unlinkable-v1`

Privacy claim:
`public-input unlinkable; transcript zero knowledge pending`

## Canonical product

- [x] Implement one fixed TS13 age-over-18 theorem.
- [x] Bind issuer, device, revocation, validity, claim, and request context.
- [x] Export the fixed-size identity-proof envelope through `proveIdentity`.
- [x] Verify the same identity theorem through `verifyIdentity`.
- [x] Remove all alternate product and TS13 public routes.
- [x] Remove alternate proof envelopes and tests for deleted paths.
- [x] Reduce FFI to identity prove and identity verify.
- [x] Remove benchmark-only FFI and JNI routes.

## Cleanup

- [x] Audit branch changes against `feat/quantum-safe`.
- [x] Delete the unused unlinkability spike feature and probes.
- [x] Delete inactive plans and implementation reports.
- [x] Remove unused helpers, aliases, and dependencies.
- [x] Finish the normative specification in Simplified Technical English.
- [x] Condense benchmark reports to verified facts.
- [x] Rewrite repository lessons as short active rules.
- [x] Finish the source-comment Simplified Technical English sweep.
- [x] Remove code that becomes unreachable after API consolidation.
- [x] Remove the standalone SHA multi-slot and window-exposure paths.
- [x] Remove the remaining unused SHA transcript and Cargo feature facades.
- [x] Collapse the redundant request, statement, proof fields, and proof alias.
- [x] Audit each cleanup diff for lost AIR constraints, relation terms, or transcript bindings.
- [x] Confirm that terminology changes do not change transcript-domain bytes.
- [x] Replace the stale SHA design note only after its live invariants are covered by code and tests.
- [x] Run a final dependency and dead-code audit.

## Canonical terminology

- [x] Use identity-proof envelope terminology outside serialized version fields.
- [x] Replace campaign labels with the component or constraint names.
- [x] Format and check the changed Rust files.

## Verification

- [x] Format all changed Rust and Kotlin files.
- [x] Pass release workspace check for all targets.
- [x] Pass release Clippy with warnings denied.
- [x] Pass release unit and integration tests.
- [x] Pass focused `proveIdentity` and `verifyIdentity` envelope tests.
- [x] Regenerate the source-bound circuit artifact and hash.
- [x] Record the canonical circuit geometry and envelope capacity.
- [x] Update the Android fixture with the new circuit hash.
- [x] Build the canonical Android binding and compile its device test.
- [x] Pass `git diff --check`.

## Audit follow-up

- [x] Make the exported invalid-witness matrix assert exact host rejection.
- [x] Add a proof-level negative for revocation endpoint equality.
- [x] Bind every Keccak round to its official index and Iota constant.
- [x] Add an adversarial test for the Keccak round-schedule binding.
- [x] Audit every preprocessed column and remove the approved exact redundancies.
- [x] Remove semantically dead committed trace columns.
- [x] Regenerate the circuit artifact and update its geometry records.
- [x] Run the complete release verification after the audit fixes.

## Performance campaign

- [x] P0: Add or verify phase timing and peak-memory measurements.
- [x] P0: Run seven cold desktop samples with timing enabled and disabled.
- [x] P0: Run timing-enabled and timing-disabled warm desktop samples.
- [x] Record latency, proof size, peak RSS, source revision, and host metadata.
- [x] P0: Build the source-bound Android artifact and run the current-circuit
  Firebase baseline on Pixel 8, Galaxy S24 Ultra, and Galaxy A54.
- [x] P1: Reduce canonical-path overhead and prove that canonical
  `proveIdentity` is at most 1.15 times the AIR-core latency.
- [x] P2: Keep the sound 25-row carrier and reduce the all-ML-DSA-65 shared
  Keccak service to at most 9,200,000 committed cells without weakening the
  round schedule, job binding, or Iota checks.
  - [x] Reject the endpoint-GKR experiment: it takes about 100 seconds at the
    canonical geometry and weakens the conservative algebraic bound by about
    4.1 bits.
  - [x] Reject the mixed ML-DSA-44 profile and the two-repetition carrier.
  - [x] Record the corrected all-ML-DSA-65 geometry in main-repository mailbox
    A-007.
  - [x] Restore ML-DSA-65 for the issuer, device, and revocation roles.
  - [x] Pin 9,102,656 committed cells, 261 permutations, the soundness bound,
    and the carrier payload.
  - [x] Pin final release latency and peak memory.
- [x] P3: Reduce private MSO and item SHA-256 to at most 1,500,000 committed
  cells without moving private-input checks outside the proof.
  - [x] Keep the all-ML-DSA-65 SHA geometry at 1,320,640 committed cells.
  - [x] Update and validate the live source-bound artifact profile.
  - [x] Pass the canonical `proveIdentity` and `verifyIdentity` release test.
  - [x] Record the seven-sample desktop result and the cold Pixel 8 delta.
- [x] P4: Measure the fixed-security PCS and FRI frontier and select the point
  that meets the mailbox-approved proof-envelope ceiling.
  - [x] Reduce the canonical CBOR maximum constraint degree from eight to four.
  - [x] Regenerate the live composition profile and pass artifact drift plus
    the canonical A1/A2/B proof path.
  - [x] Reject explicit lifting domains that cannot interpolate the live
    composition polynomial.
  - [x] Derive the exact 20-point frontier from the final P2 geometry.
  - [x] Reject all ten blowup-one points with a live pinned-STWO proof attempt.
  - [x] Measure all ten valid blowup-two and blowup-three points in serial
    fresh desktop processes.
  - [x] Package and verify all six blowup-two Android pairs.
  - [x] Package and verify all four blowup-three Android pairs.
  - [x] Measure all ten valid points on Pixel 8 with source-bound artifacts.
  - [x] Select b3 q36 p20 L19 as the fastest measured cold Pixel 8 point below
    the 2,500,000-byte ceiling.
- [x] P5: Measure Android worker counts, peak RSS, affinity, allocator, and
  available ARM acceleration; keep only improvements that help the binding
  devices.
  - [x] Add and verify phase memory, effective-worker, stack, topology, and
    benchmark-only affinity records.
  - [x] Emit the Android benchmark summary and each phase as separate bounded
    JSON records so Firebase preserves the complete result.
    - [x] Update the source-bound SDK README with the final canonical runtime
      after cleanup.
  - [x] Run the preliminary desktop worker sweep at the P4+P5 checkpoint.
  - [x] Audit existing branches for reusable affinity and allocator work.
  - [x] Trace the canonical proof memory lifetime and rank live allocations.
  - [x] Store Keccak GKR gate numerators in their canonical base-field form.
  - [x] Bound and parallelize the Keccak claimed-sum inverse scratch allocation.
  - [x] Move the padded GKR input allocations without a denominator copy.
  - [x] Replay the canonical carrier lookups from an independent trace source
    after GKR, and bind that source to the committed trace.
  - [x] Verify the private, fail-open Android affinity policy and its unit tests.
  - [x] Verify NEON dispatch in the exact AArch64 library from the current AAR.
  - [x] Sweep private Android worker and proof-thread stack sizes.
  - [x] Select six workers, a 2 MiB proof-thread stack, a 16 MiB proof-worker
    stack, and no affinity policy.
  - [x] Remove the temporary controls and hard-code the selected sizes.
  - [x] Reject the isolated Android jemalloc candidate.
    - [x] Test the maintained jemallocator releases with NDK 27.
    - [x] Remove the candidate after the AAR cross-build failed.
    - [x] Record the toolchain errors and the absence of candidate artifacts.
  - [x] Run the worker, affinity, allocator, RSS, and NEON device sweep
    on the selected P4 circuit.
- [x] P6: Skip witness-generation parallelism because the fixed-scope
  feasibility analysis showed that it cannot meet the three-phone target.
- [x] Regenerate and verify the source-bound artifact after every accepted
  soundness-affecting change.
- [x] Run the complete release, Clippy, formatting, artifact-drift,
  soundness-negative, and unlinkability-negative test matrix.
- [x] Run the final desktop campaign and the final Firebase three-device
  campaign through the canonical `proveIdentity` and `verifyIdentity` API.
- [ ] Meet the primary mobile gates: cold prove below 2,000 ms on Pixel 8,
  Galaxy S24 Ultra, and Galaxy A54; verify at most 500 ms; use a fixed
  credential-independent envelope; and meet the mailbox-approved proof-size
  ceiling.
  - [ ] Meet the 2,000 ms cold-prove target on all three phones. The final
    canonical matrix failed this target on all three phones.
  - [x] Keep verification at or below the approved 500 ms limit on all three
    phones.
  - [x] Keep one fixed, credential-independent 1,507,374-byte envelope.
  - [x] Keep the envelope below the 2,500,000-byte ceiling.

## Invariants

- Keep the fixed TS13 theorem and identity-proof envelope.
- Keep the credential-independent public-input surface.
- Keep one ISO MSO 1.0 circuit path.
- Accept valid `IssuerSignedItem` map-key permutations.
- Keep `proveIdentity` and `verifyIdentity` as the only application API.
- Do not add STWO transcript masking in this campaign.
- Benchmark only the final soundness-checked artifact and canonical `proveIdentity` path.
- Regenerate the circuit hash after all source cleanup.

## A-013 committed-bit redesign reconciliation

- [x] Read A-013, Q-013, Q-012, Q-011, and every linked design in full.
- [x] Audit the redesign against the normative TS13 theorem and privacy model.
- [x] Compare the redesign with the live soundness source and artifact `e3426e32…`.
- [x] Record the frozen layered-Keccak APK's exact provenance and quarantine status.
- [x] Reject the missing committed-bit v3 and retain the accepted committed-nibble path.
- [x] Receive Lucas's authentication confirmation and pass the A-014 bucket probe.
- [x] Run one parallel three-phone matrix with the final c7 APK pair.
- [x] Record exact phone metrics and reconcile the final campaign evidence.

Audit result: A-013 is an interim decision, not an implementation design. Its
promised v3 was never issued and its literal 108-bit gate is stale. A-015 and
A-016 permanently retire that route and accept the committed-nibble design.
Circuit `e3426e32…` and its APK pair are historical throughput-only artifacts.
Final acceptance evidence must use circuit `c7c99e7b…` and its final package.

## C7 phone regression recovery

- [x] Compare the P5 and c7 phone profiles phase by phase on all three phones.
- [x] Map the measured regression to exact live source and geometry changes.
- [x] Audit existing branches and the current `post_interaction_proof` path for
  a reusable sound optimization.
- [ ] Implement the smallest structural fix that improves all three phones.
- [ ] Preserve the fixed theorem, all ML-DSA-65 roles, public-input
  unlinkability, local proving, pinned STWO and PCS settings, the fixed
  envelope, and the two-function API.
- [ ] Pass the full release, adversarial, artifact, and desktop gates.
- [ ] Regenerate the source-bound AAR and APK pair after each accepted source
  change.
- [ ] Rerun one parallel matrix on Pixel 8, Galaxy S24 Ultra, and Galaxy A54.

The first hard gate is no regression from the P5 matrix on any phone: 5,450 ms
on Pixel 8, 2,755 ms on Galaxy S24 Ultra, and 5,853 ms on Galaxy A54. Do not
start application integration while c7 remains 1.6 to 2.5 times slower than
that checkpoint. The later target remains below 2,000 ms on every phone.

The regression is confined to `post_interaction_proof`. The c7 path replaces
253 built-in GKR sumcheck rounds with 1,410 custom rounds. A measured serial
cutoff for small rounds increased the six-worker desktop post-proof median
from 1.160 seconds to 1.208 seconds, so it was removed. Table streaming cannot
provide the required 2.09x to 4.67x phase speedup. Mailbox Q-018 requests the
open authenticated-MLE engine design or confirmation that the branch must
restore P5 before further redesign work.

## Pre-layered performance checkpoint

This section records the P5 checkpoint before the authorized layered Keccak
redesign. At that checkpoint, the 2,000 ms cold-prove target failed on all
three phones and P6 was out of scope. The later layered Keccak section
supersedes each use of "final" in this checkpoint.
The Android jemalloc candidate is rejected because the maintained bindings do
not build with NDK 27 without a local patch or linker shim.

The accepted P5 memory changes are commits `fff7a631` through `c3e4ff58`.
They keep the proof, transcript, verifier, PCS parameters, and public API
unchanged. The exact-tree review passed 21 unit tests and 35 service tests in
release mode. It also passed release Clippy, formatting, and diff checks.
Tests confirmed exact leaf, GKR proof, coefficient MLE, transcript, and worker
parity. The final desktop comparison measured a 68.25 MiB peak-RSS reduction
and a 0.8 percent proving-time increase. The proof envelope stayed at
1,572,910 bytes.

The P5 mobile runtime sweep completed 13 Firebase matrices and 39 phone
executions. All executions passed the exact circuit-hash, envelope, runtime,
stack, phase, verification, and target-log checks. The sweep selected six
workers, a 2 MiB proof-thread stack, a 16 MiB proof-worker stack, and no
affinity policy. The fixed A/B/B/A rule rejected the affinity policy because
Galaxy S24 Ultra did not improve by more than the measured pair spread.
The campaign retained six workers because neither four nor eight workers
improved all three binding phones. This selection is not a statistical
optimum.

The no-affinity A-row mean reduced peak HWM by 18.2 percent on Pixel 8, 19.9
percent on Galaxy S24 Ultra, and 18.5 percent on Galaxy A54 relative to the P4
selected-point matrix. The cold proving results had high variation and did
not show a stable latency improvement. No P5 row met the 2,000 ms prove gate.
The fastest measured values were 4,986 ms on Pixel 8, 2,618 ms on Galaxy S24
Ultra, and 5,638 ms on Galaxy A54. Product cleanup, final artifact
regeneration, the full verification matrix, and the final canonical
three-phone gate are complete.

The final soundness-source checkpoint is `13a1a51d`. The source-bound artifact
commit is `a34ac578`. The final package source and mobile fixture commit is
`a91085dc`. The final circuit hash is
`2eff9e073151b4bce733516f4b6dd411b6d48ef5425fd93d41c64bedf524fea9`.
The product has no temporary runtime controls.

Final package 3 has these SHA-256 values:

- AAR:
  `cdd744130c540f8ba910843b2a0fafe482714b864c200c06ee375c7aa6f242fa`
- Host APK:
  `b126d7693abb8079b2412a0ba1590124f16252ed61449d96e0b86f5aec3e6766`
- Test APK:
  `050ddfca27695d32c1c6e1d563ec76a1f16ad2d9551f497e877e5cd839678ae3`
- Fixture:
  `c9fe96c76b13a884afb324e68dd939561c8d4664fe59e8cdfc85e8bf0625ea52`
- AAR and host APK arm64 library:
  `aedf9b1e6213e6d0bc7bf5b2cd20e51a5908eee5cee844b7e11bbcf87533dc38`

The final desktop campaign ran seven serial samples. It measured a 1,162 ms
median prove time and a 17 ms median verify time. The first verify time was
42 ms. The proof envelope was 1,572,910 bytes.

The final Firebase run was matrix `matrix-92u1aei93c81a`, numeric ID
`4904946063125125660`, in history `bh.f5f036aa81c4230a`. All phones used API
34, six actual Rayon workers, a 2,097,152-byte proof-thread stack, a
16,777,216-byte proof-worker stack, and 25 phase records. The exact final
results were:

| Phone | Prove | Verify | Peak HWM |
| --- | ---: | ---: | ---: |
| Pixel 8 | 5,450 ms | 239 ms | 1,346,468 KiB |
| Galaxy S24 Ultra | 2,755 ms | 140 ms | 1,414,276 KiB |
| Galaxy A54 | 5,853 ms | 255 ms | 1,338,168 KiB |

Each execution returned `OK (1 test)` with a 1,572,910-byte envelope. No
execution had an OOM, crash, or ANR. The verification and envelope gates
passed. The 2,000 ms prove target failed on all three phones.

All normal release workspace tests passed. All 18 ignored release tests
passed. Release Clippy passed with warnings denied. Formatting, the release
build for all targets, the quantum-only dependency check, the source-bound
artifact check, and the diff check passed.

## Mobile prove-gate continuation

- [x] Reconstruct the final per-phase phone profile and quantify the gap to
  2,000 ms.
- [x] Audit the active prover and existing branches for reusable,
  soundness-preserving work.
- [x] Reject another fixed-scope implementation because no measured candidate
  can materially reduce the binding phone times.
- [x] Quantify the proof-identical backend ceiling and the minimum geometry
  budget for a structural AIR redesign.
- [x] Obtain user direction to request a staged AIR redesign that preserves
  every theorem, unlinkability, soundness, API, and local-proving property.
- [x] Send the complete redesign brief as main-repository mailbox Q-011.
- [x] Receive A-010 authorization for an AIR-only redesign with the pinned
  STWO backend and all theorem, security, privacy, and deployment invariants.
- [x] Review the Q-011 redesign and its property ledger before implementation.
  - [x] Reject the v1 design because its Keccak proof is incomplete, its
    inverse-NTT argument permits M31 aliases, and its NTT and SHA budgets do
    not match their stated column layouts.
  - [x] Send the exact correction request as main-repository mailbox Q-012.
- [x] Obtain independent acceptance for the current K candidate before using
  it as soundness evidence.
  - [x] Reject A-012's K-only design because its private bit oracle has no
    terminal commitment, its theta and boundary maps conflict, and deleting
    the old carrier disconnects the retained schedule and LogUp graph.
  - [x] Send the exact K-prototype correction request as main-repository
    mailbox Q-013.
  - [x] Complete the pre-quarantine internal K audit and track the candidate
    design in `docs/ts13-keccak-layered-gkr.md`.
  - [x] Pass a second pre-quarantine code review of the candidate.
  - [x] Read A-013 and quarantine the current committed-nibble design.
  - [x] Read A-015, suspend the committed-bit v3 design, and promote the
    committed-nibble design to an acceptance candidate.
  - [x] Receive and reconcile the independent A-015 review.
  - [x] Resolve the whole-system soundness and A54 sub-gate conflict in A-016.
  - [x] Select the truthful source-digest and payload-shape binding for F-1.
  - [x] Add the exported off-domain input-nibble negative required by F-2.
  - [x] Record the removed carrier baseline provenance required by F-3.
- [x] Implement and measure each authorized redesign stage at its hard stop
  gate.
  - [x] Build one layered Keccak acceptance candidate and delete the carrier,
    round AIR, schedule table, AndNot table, split tables, and generic GKR
    codec.
  - [x] Bind 400 committed input nibbles and the committed output through two
    outer-STARK MLE components.
  - [x] Reduce the service to five components and three claimed sums.
  - [x] Remove product-dead SHAKE-128 absorb columns and lookup entries.
  - [x] Confirm that every retained Keccak preprocessed column is active.
  - [x] Pass the complete layered adversarial freeze matrix.
  - [x] Measure desktop throughput through `proveIdentity`.
  - [x] Reduce the three-sample desktop throughput median from 8,243 ms to
    1,810 ms.
  - [x] Retire the unmeasurable complete-Keccak A54 sub-gate under A-016.
  - [x] Measure the full cold `proveIdentity` gate on all three phones.
- [x] Regenerate and verify the source-bound artifact after each retained
  acceptance-candidate source change.
- [x] Pass the complete release and unlinkability consistency checks for the
  quarantined acceptance candidate.
- [x] Build and verify one source-bound AAR and APK pair for throughput data.
- [x] Record the quarantined package provenance in mailbox Q-015.
- [x] Receive A-015 acceptance of the package provenance.
- [x] Receive the Google Cloud login confirmation and pass the bucket probe.
- [x] Commit F-1 through F-3 before artifact generation.
- [x] Regenerate the source-bound artifact, circuit hash, and fixture after
  the F-2 source change.
- [x] Build the source-bound AAR and APK pair for the final circuit hash.
- [x] Rerun all release, ignored, negative, unlinkability, and artifact tests.
- [x] Run one exact three-phone acceptance matrix with the final APK pair.

## Layered Keccak review

The acceptance candidate uses 400 committed spread-nibble columns, an
18-variable grouped extraction and validity sumcheck, carried wiring
functionals, and two source-bound log-9 MLE components. The replacement adds
212,992 cells. The complete Keccak service uses 1,534,720 cells after removal
of product-dead SHAKE-128 absorb columns and lookup entries. Its conservative
same-accounting error is `8468/(q-2)`, below the removed carrier's `8974/q`
contribution. A-015-review independently accepts the protocol as sound and
reports no critical or high finding.

A-013 quarantined this package after it selected a committed-bit route. A-015
suspends that route and promotes this committed-nibble design to an acceptance
candidate. A-015-review accepts the protocol as sound with no critical or high
finding. It requires F-1 through F-3 before final acceptance. F-2 changes the
soundness source, so the old artifact and package remain throughput evidence
only. A-016 requires unchanged-or-improved algebraic soundness under identical
accounting and records the live baseline at about 105.91 bits. It retires the
unmeasurable A54 complete-Keccak sub-gate.

The candidate release freeze passed 30 layered-library tests and 31 service
tests. The matrix includes row swaps, cross-permutation source attacks,
alternate Iota, SIMD equivalence, invalid nibbles, and canonical mutations in
all 147 payload sections.

The candidate source commit is `2111a1eb`. Its source-bound artifact commit
is `5a619bf2`. The circuit hash is
`3fac167754de85508fd6fda45e37043f6e104821463b9fa40e17d88fa4938b9c`.
The identity-proof body capacity is 1,507,328 bytes.

The locked consistency matrix passed all normal workspace tests and all 18
ignored tests. It also passed these gates:

- The exact A1/A2/B test.
- The 17-case exported-prover rejection matrix.
- The three-test live artifact target.
- The exact public schema test.
- Release Clippy with warnings denied.
- Formatting and the quantum-only dependency check.
- The artifact-drift check.

These results apply only to the old circuit hash. They cannot serve as final
acceptance evidence after the mandatory F-2 source change.

Seven separate desktop processes measured these `proveIdentity` times in
milliseconds: 1,768, 1,834, 1,774, 1,852, 1,860, 1,784, and 1,782. The median
was 1,784 ms. The median `verifyIdentity` time was 80 ms. Every proof envelope
was 1,507,374 bytes. The measured maximum resident set size was 777,682,944
bytes. The desktop median is 78.4 percent lower than the 8,243 ms layered
baseline.

The desktop host was a 12-core Apple M2 Max MacBook Pro with 32 GB of memory
and macOS 26.5.2. The Rust compiler was nightly 1.94.0 from 2026-01-14. The
probe SHA-256 was
`123b93f5909dcf39d5a470731692210460549e89a157da4b3541607447415845`.
The `Cargo.lock` SHA-256 was
`220b0810dc0423085bb2654fd738ee5d0ee71ca8e61cf971ae38edc128ff87ff`.

The candidate package has these SHA-256 values:

- AAR: `d91605ae10f60757fe1db60a0bd4e08b1928a7e94531af05d75ca5f0e3e31501`
- Host APK: `4c7a70bf62f11c1fbcccb5aa8c121b778518f8c7bfbc945ae73d576ff33ec614`
- Test APK: `d959332c98d7d47231258912a89dfd5eebcdb400cc3ed78bb58564b49518ea19`
- Fixture: `3776028d3821a5242578f8f9878d44e5c680d0f0f5626135f05d22eb00efc32a`

The AAR and host APK contain the same ARM64 library. The test APK contains the
exact checked-in fixture. The fixture names only `proveIdentity` and
`verifyIdentity` and binds the old candidate circuit hash. A final-hash
three-phone matrix used only the final-hash package. The old package remains a
throughput checkpoint because F-2 required a code change and new circuit hash.

The post-review soundness-source commit is `cf8f2cec`. The artifact and fixture
commit is `c2923bac`. The final circuit hash is
`c7c99e7b6e7cddbfc27617b2597bea1315ebd39e34ed08c564d67220282af9bc`.
The full release matrix passed, including all 18 ignored tests, the focused
unlinkability and negative tests, the 30-test layered freeze, and the 31-test
service freeze.

The final AAR and APK pair passed library, fixture, circuit-hash, and API
parity checks. The final seven-process desktop median is 1,780 ms for proving
and 81 ms for verification. The maximum resident set size is 786,415,616
bytes. Every proof envelope is 1,507,374 bytes. Detailed evidence and package
hashes are in `tasks/bench-results/ts13-layered-final-20260802`. The final
three-phone matrix is `matrix-5gyixcf0k5kxa`. All three tests passed. The
phone prove times were 13,560 ms on Pixel 8, 5,075 ms on Galaxy S24 Ultra,
and 9,523 ms on Galaxy A54. All three phones failed the 2,000 ms prove gate.
All three passed the 500 ms verify gate, the fixed-envelope gate, and the
runtime-shape gate.
