# Quantum-safe-only proving campaign

Branch: `feat/quantum-safe`
Baseline: `ce26b934` (S9)

## Final Android 15–20% campaign (2026-07-24)

- [x] Pack paired coefficient rows without aliasing the second coefficient's
      norm-high limbs.
- [x] Replace dry interaction traces with exact range/stream metadata
      generation and cache shared sponge outputs.
- [x] Prepare issuer, device, and revocation witnesses concurrently while
      preserving deterministic role and transcript order.
- [x] Validate the safe candidate in two counter-ordered, same-APK Firebase
      matrices on A54, Pixel 8, and S24 Ultra using big cores only.
- [x] Batch Round-GKR inversions globally and retain packed leaves only after
      exact legacy/transcript equivalence, full release suites, host A/B, and a
      separate two-matrix phone A/B all passed.

### Review

- The safe candidate improves full ML-DSA identity-plus-TS13-revocation proving
  by 20.3% / 18.1% / 26.3% on A54 / Pixel 8 / S24 Ultra. All 48 proofs verify;
  candidate cold/warm verification medians are 63–98 ms / 18–29 ms.
- Packing the already-present Round-GKR leaves and globally batching its
  inversions adds 1.5% / 5.1% / 16.8%, with median adjacent savings of
  67.5 / 33 / 184.5 ms. This is not a GKR-versus-direct-LogUp comparison.
  Its 48/48 proofs verify, worst warm verification is 32 ms, and proof size
  plus peak memory remain within noise.
- Full release verification passes for `stwo-keccak`, `stwo-mldsa`,
  `eu-id-prover`, and `eu-id-ffi`, including composed adversarial cases and
  the real ignored full-PQ FFI round trip. Production-feature Clippy,
  touched-file formatting, Android unit/build/lint, APK signing, provenance,
  big-core affinity, and both strict analyzers pass.
- Reports:
  `tasks/bench-results/euid-mldsa-safe-ab-20260724T015527Z/analysis.md` and
  `tasks/bench-results/euid-mldsa-roundgkr-ab-20260724T021803Z/analysis.md`.

## Final residual-cell sweep

- [x] Flatten the shared Keccak sponge interaction fractions, use one packed
      batch inversion, and prove byte-identical columns/claimed sum against the
      legacy materializer.
- [x] Discard the sponge change: 16×16 alternating host A/B measured only
      0.46% paired gain and 2.5 ms median saving, below both 1% and 8 ms.
- [x] Implement and test a seven-domain proof-wide range provider that removed
      21 hosted components and 182,528 committed M31 cells; discard it after
      the strict host retention gate failed.
- [x] Add exact old/new multiplicity aggregation, first-excluded rc4/rc11
      negatives, paired cross-bound aliases, missing/shared-claim, root, and
      transcript regressions.
- [x] Stage and validate the TS13 v8 repin plus tree-0 cache-key v3, then restore
      v7/cache-key v2 when the candidate was rejected.
- [x] Pass the full Keccak, ML-DSA, prover, FFI, touched-file formatting,
      production Clippy, standalone identity, and exact host A/B gates.
- [x] Stop before Android/Firebase: two 16×16 host ABBA blocks combined to only
      0.764% paired geometric gain and 7 ms raw median saving, below the
      required 1% / 8 ms gate.
- [x] Reject static-selector pruning for this release: ML-DSA static columns
      save 135,936 cells; adding generic Keccak schedule compaction raises the
      ceiling to 168,064 (199,584 with optional trace enablers), but removes no
      components and prices at only ~1–2% for substantially broader AIR and
      TS13 churn.

### Residual-sweep review

- The range candidate passed 219 active core/prover release tests, 11 active
  FFI tests, the ignored real full-PQ FFI round trip, warnings-denied Clippy,
  and exact standalone preprocessed/layout comparison against the preserved
  pre-change release library.
- Its paired Rc4→Rc13 and Rc11→Rc13 attacks were constructed so erasing bound
  tags would balance exactly; with the production tags retained both reject.
  Attack state was snapshotted into immutable relation objects so Rayon workers,
  interaction generation, and verifier reconstruction evaluated one identical
  forged multiset.
- Host block 1: baseline/candidate medians 590.5/582 ms, paired geometric gain
  0.537%, median pair saving 8 ms. Block 2: 588/581 ms, 0.990%, 10 ms.
  Combined: 588.5/581.5 ms, 0.764%, raw median saving 7 ms, 24 wins / 1 tie /
  7 losses. The candidate therefore failed the predeclared host retention gate
  and was reverted without an Android build.
- The surgical rollback restored the five-domain coefficient table (tags 0–4,
  padding 5, 9,091 active rows), local decomposition/SampleInBall providers,
  hosted public/private claim lengths 15/18, tree-0 cache key v2, and TS13 v7
  hash `375954cc8370dd241c5bc3ecce8da5c447edfe4c720e6dc786a7353ef0985919`.
  Independent source review found no seven-domain routing, alias hook, attack,
  v8 identity, or cache-v3 residue.
- The restored frontier passed 209 active Keccak/ML-DSA/prover release tests
  (one benchmark ignored), 11 active FFI tests, the ignored production-shaped
  full-PQ FFI round trip, warnings-denied production Clippy, touched-file
  rustfmt, and `git diff --check`. Its rebuilt `pq_perf_probe` is byte-for-byte
  identical to the preserved pre-experiment Round-GKR binary:
  `754cb2ae3c59dfa04a48a2481f1f61cf62a10f4ad6e553c79edde66ed8f55d10`.

## Work order S1 — ML-DSA soundness remediation

- [x] Establish `s1/soundness-remediation` at `feat/quantum-safe` `ae087857`.
- [x] Repair the decomp final-row hint accumulator tie and replace the false-pass negative.
- [x] Make public MSO and private IssuerSignedItem semantic bindings fail closed.
- [x] Bind the SDK contract labels and provide a real TS13 proof/profile verifier.
- [x] Keep revocation range witness state out of every serialized verifier envelope.
- [x] Pin all standalone ML-DSA verifier policy/configuration inputs.
- [x] Bound untrusted SDK envelope/decompression decoding.
- [x] Batch the v6 TS13 compatibility update and legacy typed rejections.
- [x] Run the release suites, privacy/negative matrix, and one-thread acceptance probe.

### Review

- The shared hint accumulator now ties its final base-cell value to the
  interaction running sum before the RC8 bound is applied; the forged
  accumulator-split regression is rejected during proving.
- The verifier rederives canonical IssuerSignedItem `elementIdentifier` and
  `elementValue` anchors, including canonical definite nationality-array member
  stride. Product labels and scope are fail-closed, and standalone ML-DSA
  verifiers pin both PCS policy and canonical tree-0 roots.
- TS13 has a dedicated V1 proof envelope and real equality/revocation proving
  entry point. The private revocation range is skipped in all serialized
  verifier statements/artifacts; an end-to-end fully-PQ TS13 equality proof
  verifies from the public-only envelope and rejects a changed epoch.
- Verification completed with `RAYON_NUM_THREADS=1`: all `stwo-mldsa`, mdoc,
  and SDK suites; strict clippy for the three changed crates; and the release
  `pq_perf_probe`.

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
- [x] Run adversarial constraint tests, full quantum gates, and same-session A/B benchmarks.
- [x] Commit and push Q3 (`cc846a70` core; measured review follow-up).

## Campaign rails

- Do not edit the user's main checkout or classical branches.
- Do not touch `stwo-mldsa::coeffs`; its Horner interaction requires `bound == log + 1`.
- Preserve the local Stwo `8c998390` composition-split patch until an equivalent remote pin exists.
- Preserve production `(1,4,26,2)` with PoW 25 (129-bit PCS label). Do not present that label as
  whole-system 128-bit PQ soundness; the current conservative TS13 composed label is 82 bits.
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
- Q3 product verification: all 37 `eu-id-prover` tests pass in 274.28 s, plus all 15 SDK/FFI tests.
  The shape dump confirms the merged SHA is exactly 951 columns at log 9: 12 preprocessed, 519
  trace, and 420 interaction columns.
- The initial same-session A/B accidentally omitted `RAYON_NUM_THREADS=1`; it therefore measured
  default-Rayon multithreaded proving. Those samples were baseline 2,418/2,487 ms versus Q3
  1,789/1,811 ms and must not be presented as the one-thread campaign metric.
- Corrected five-run A/B with `RAYON_NUM_THREADS=1` against parent `4c25c72d`: baseline medians are
  8,573 ms prove, 16 ms verify, and 1,113,514 bytes; Q3 medians are 6,995 ms, 15 ms, and 1,081,410
  bytes. Median proving improves 18.4% and proof size improves 32,104 bytes (2.88%). The probe now
  prints `rayon_threads` on every result line so thread-count drift is visible.

## Milestone Q7 — close the hard full-PQ prove gate

Hard acceptance command: `RAYON_NUM_THREADS=1 cargo run --release -p eu-id-prover --example
pq_perf_probe` using `mdoc_production_pcs_config()` and ML-DSA-65 for issuer, device, and revocation.

- [ ] Prove in less than 1,000 ms.
- [x] Verify in less than 100 ms; never regress.
- [x] Proof below 1,000,000 bytes; never regress.
- [x] Capture a fresh instrumented baseline before changing code.
- [ ] Select an architecture-level optimization with enough measured leverage to close the gap;
      do not substitute a sequence of small-fry changes whose priced total cannot reach the gate.
- [ ] Implement the smallest sound version and add a focused adversarial regression.
- [ ] Run focused suites, workspace checks, and the exact acceptance probe.
- [ ] Iterate until all three gates pass in the same run.

Fresh Q7 baseline (`73ac7d4e` plus task-document edits, 2026-07-15): prove 5,972 ms, verify 15 ms,
proof 981,346 bytes. Prover phase census: tree0 commit 378 ms; tree1 write+commit 1,166 ms; tree2
write+commit 1,601 ms; component build 322 ms; composition+FRI+open 2,287 ms. The existing coeffs
range-relation unification is priced at only 0.5–0.8 s, so it is insufficient as the primary Q7
lever. The next implementation must attack commitment/FRI cost or delete multiple ML-DSA-sized
proof workloads while preserving the public verification contract.

Retracted Q7 result (2026-07-15): the 297/299/303 ms measurements moved all ML-DSA verification
outside the STARK and changed PoW25/query26 production PCS to PoW0/query32. Those runs violate the
required trust boundary and fixed production configuration and are not acceptance evidence. The
independent SHA `Range16` → `Range8` AIR optimization remains eligible only after the fully hosted
composition and original PCS are restored and re-verified.

## Milestone Q8 — full-PQ soundness repair before performance work

- [x] Audit the production verifier, tree-0 trust anchor, all ML-DSA public inputs, hosted message
      bridges, signature-witness contract, revocation privacy boundary, shared lookups, and PCS.
- [x] Make the ordinary product verifier reconstruct the canonical tree-0 commitment internally;
      remove external-root trust and every path that accepts the proof's own root as authority.
- [x] Prove `tr = SHAKE256(pkEncode(rho, t1), 64)` inside the hosted STARK for issuer, device, and
      revocation; do not replace this with native signature verification.
- [x] Add focused adversarial regressions for unpinned tree 0, wrong `tr`, and Range8 byte forgeries.
- [x] Run the affected release suites and the exact production probe with canonical tree 0.
- [ ] Resume prove-time optimization only after every soundness gate passes.

New P0s found during the completed full pass:

- [x] Restore exact SampleInBall sign-bit binding to the first eight SHAKE bytes.
- [x] Constrain the ordered FIPS rejection-sampling state (`i` start/hold/increment/final).
- [x] Bind the read/write flag through the SampleInBall memory permutation.
- [x] Add exploit-shaped sign, skip-valid-byte, reordered-accept, and sorted-write negative tests.
- [x] Enforce canonical public `t1 < 2^10` and bounded/derived SIB shape claims.
- [x] Replace unauthenticated per-proof root provisioning with canonical verifier reconstruction.
- [x] Remove the Keccak GKR/native-verifier boundary and restore direct Keccak round LogUp constraints
      in the outer STARK; require zero post-interaction payload bytes in production.
- [x] Bind `perm_id` and canonical `round_idx → round_idx+1` in every Keccak round link, with
      cross-permutation-swap and round-reordering negative tests.
- [x] Move the ML-DSA folded-identity accept/reject condition from `verify_post_interaction` into an
      outer-STARK component and add a mutated-group-evaluation negative test.
- [ ] For the literal all-arithmetic-in-AIR target, prove `ExpandA(rho)` / public matrix evaluation
      rather than treating it as deterministic verifier-side public preprocessing.

Initial audit verdict (2026-07-15): the restored three-instance composition was not shippably sound.
The normal `verify_mdoc_circuit` path passed no expected preprocessed root, so prover-selected tree-0
content could replace the public ML-DSA message, schedules, selectors, and range tables. Issuer/device
also accepted a free public `tr` instead of proving its FIPS public-key hash. Canonical tree-0
reconstruction and in-proof public-key hashing now close those concrete failures. The folded identity
is now an outer-STARK constraint, but its public `ExpandA(rho)` matrix values remain deterministic
verifier-derived parameters rather than a traced computation. Signature fields are currently
existential witness values: the proof establishes that a
valid signature exists under each exact public key/message, not equality to serialized COSE signature
bytes. Revocation bounds are also serializable in the current statement/artifact API, so privacy is
not fail-closed at that boundary.

The advertised `26 * 4 + 25 = 129` bits covers only Stwo's PCS query/PoW formula. The repository has
no completed composed bound for FRI, OODS/polynomial identities, every LogUp relation, Fiat–Shamir,
Merkle binding, and their union. TS13 now publishes the enforced `(4,26,25)` tuple and a conservative
82-bit composed label rather than claiming the 129-bit PCS label is the whole proof. The proof uses
Blake2s-256 for both transcript and Merkle commitments: its quantum preimage cost is about 2^128,
but generic quantum collision cost is about 2^85. Therefore the current system must not be described
as a demonstrated 128-bit post-quantum commitment-binding proof without a separately accepted hash
security model or wider-hash migration.

Q8 implementation result (2026-07-15): ordinary mdoc/TS13/SDK verification is fail-closed and
reconstructs canonical tree 0 from the public statement and bounded proof shape. Each hosted ML-DSA
instance adds a fourth Keccak job for `SHAKE256(pkEncode(rho,t1))` and LogUp-binds its first 64
squeeze bytes to public `tr`. SampleInBall now binds its sign bits, ordered rejection-sampling state,
and read/write classification. Release gates pass: 149 active `stwo-sha256` tests (19 ignored), 80
active `stwo-mldsa` tests (1 ignored), all 34 `eu-id-prover` tests, and all 13 SDK library tests.

Four final exact probes, each release with `RAYON_NUM_THREADS=1` and production `(4,26,25)`, measured
5,230–8,907 ms prove, 283–291 ms verify, and 966,186–972,122 bytes. Only proof size passes. Canonical
tree reconstruction is included in verification and exposes a real >100 ms regression; proving
remains 5.2–8.9x over the hard gate.

Canonical tree-0 follow-up (2026-07-15): production mdoc, SDK, and TS13 verification no longer
accept or serialize an externally provisioned preprocessing root. The verifier rebuilds the exact
tree from the public statement and bounded proof shape using the same module order and shared SIB
preprocessing generator, then compares commitment 0 internally. The full revocation-enabled release
e2e and adversarial root/SIB/t1 regressions pass. Exact single-thread production probing measured
5,230–8,907 ms prove, 283–291 ms verify, and 966,186–972,122 bytes. Proof size passes, but canonical
reconstruction regresses verification above the 100 ms rail and proving remains far above 1,000 ms;
this is a soundness baseline, not acceptance completion. A fast follow-up must remove
statement-dependent tree-0 content or add at least two independently challenged PCS-bound
canonical-equality openings; one QM31 OODS equality has only about 108 bits at degree 2^16 and is not
a 128-bit replacement.

Pure-STARK correction (2026-07-15): production no longer serializes or verifies a Keccak GKR payload.
All 898 round lookups per row are direct outer-AIR LogUps; the relation now includes permutation id and
round index, and the ML-DSA folded identity is an AIR constraint. Batch-four LogUp accumulation keeps
the fixed production PCS and prioritizes proving speed over wire size. Two exact
`RAYON_NUM_THREADS=1` production probes measured 7,253–8,020 ms prove, 276–301 ms verify,
1,061,322–1,064,314 bytes, and zero auxiliary payload bytes. All three performance rails still fail,
but proving is roughly twice as fast as the batch-16 size-first baseline. `ExpandA(rho)` remains
public verifier preprocessing, so the stronger literal requirement that every public derivation
itself be traced is still open.

Batch-two experiment (2026-07-15): lowering the same direct LogUp to batch two passed all 14 Keccak
service adversarial tests but measured 18,125 ms prove, 683 ms verify, and 1,187,210 bytes. Doubling
the interaction width overwhelmed the lower constraint degree, so the experiment was rejected and
batch four restored as the fastest measured sound setting.

## Remote plus soundness-only reconstruction

- [x] Classify every remote-to-worktree change as soundness, required support, or performance-only.
- [x] Reconstruct `origin/feat/quantum-safe` plus only the soundness closure in an isolated worktree.
- [x] Run focused correctness gates and the exact single-thread production probe.
- [x] Record the measured result and remove the isolated worktree.

Review (2026-07-15): the exact isolated variant starts at remote `132ae612`, cherry-picks none of
the nine local commits, retains the remote direct batch-four Keccak LogUp and Range16 SHA tables,
and adds only canonical tree-0 reconstruction plus the ML-DSA/Keccak/SampleInBall/folded-identity
repairs. It excludes the GKR/payload plumbing, the `2f5d4ec2` heap-allocating evaluator refactor,
and the SHA Range16-to-Range8 optimization. The focused canonical tree-0/public-shape release
regression passed. Two exact release probes with `RAYON_NUM_THREADS=1` and production `(4,26,25)`
measured 6,618–7,360 ms prove, 415–421 ms verify, and 1,090,882–1,094,466 bytes.

## App integration FFI parity

- [x] Mirror the `feat/proof-reductions` production UniFFI entry-point names.
- [x] Preserve the quantum-safe ML-DSA statement and trust-pin fields.
- [x] Update Kotlin integration examples and boundary tests.
- [x] Run SDK/FFI checks and review the complete checkpoint before commit and push.

Review (2026-07-15): the production UniFFI surface now exports `prove_identity` and
`verify_identity`, generating Kotlin `proveIdentity` and `verifyIdentity`, exactly as on
`feat/proof-reductions`. The quantum-safe contract deliberately keeps
`issuerPublicKeyHash` and `trustedIssuerPublicKeys`; it does not restore the legacy P-256 fields or
the externally supplied tree-0 root. Host UniFFI generation confirmed those names and fields.
Formatting, workspace clippy with warnings denied, all 14 SDK library tests, both FFI library tests,
all 14 Keccak service tests, all 11 SampleInBall tests, and the focused canonical-tree mdoc release
test pass. The final exact release probe with `RAYON_NUM_THREADS=1` measured 9,802 ms prove, 434 ms
verify, 1,091,754 bytes, and zero post-interaction payload bytes. This is an app-integration and
soundness checkpoint, not completion of the three performance rails.

## Milestone Q9 — prove `ExpandA(rho)` inside the STARK

- [x] Trace the current verifier-derived matrix evaluations through the folded ML-DSA identity.
- [x] Specify the minimum SHAKE128 `RejNTTPoly` AIR and its binding to public `rho` and matrix cells.
- [x] Add an exploit-shaped regression that substitutes a self-consistent forged matrix.
- [x] Implement the derivation by reusing the existing Keccak service and lookup machinery.
- [x] Run focused ML-DSA/Keccak adversarial suites and workspace checks.
- [x] Run the full issuer/device/revocation release proof with `RAYON_NUM_THREADS=1` and record the
      resulting prove, verify, proof-size, and payload measurements.

Scope: remove the remaining deterministic `ExpandA(rho)` verifier-preprocessing boundary. The
existing ISO 18013-5 `deviceSignature` binding remains unchanged. This milestone does not change the
fixed production PCS configuration or weaken any issuer/device/revocation ML-DSA constraint.

Review (2026-07-15): `rho` now feeds 30 mixed-mode SHAKE128 service jobs; an ordered RejNTT AIR
consumes every full squeeze block and yields exactly 256 accepted canonical NTT coefficients per
matrix polynomial. A second component proves all eight inverse-NTT butterfly stages, exact modular
multiplication with range-checked limbs/quotients/carries, final `256^-1` scaling, and the balanced
base-512 bivariate evaluations used by the folded identity. The native verifier no longer derives or
selects `A`; it only consumes the 30 lookup-bound evaluations. Candidate counts are bounded,
transcript-mixed public schedule data, and tree 0 remains verifier-reconstructed.

Adversarial regressions reject a post-proof matrix-evaluation change, a rejection-count change, a
malformed count vector, and—critically—a malicious prover whose forged `A_hat` and inverse transform
are internally self-consistent but disconnected from the SHAKE128/RejNTT cells. Release results:
42/42 `stwo-keccak` tests; 86/86 active `stwo-mldsa` tests (1 ignored); the full three-role mdoc e2e;
the hosted malformed-claim matrix; and clippy across all relevant targets with warnings denied.

Two exact production probes after the repair, both `RAYON_NUM_THREADS=1`, release, `(4,26,25)`,
measured 20,706–24,364 ms prove, 687–938 ms verify, 1,227,262–1,229,246 bytes, and zero auxiliary
payload bytes. This closes the remaining all-arithmetic-in-STARK boundary but fails every performance
rail. It is a soundness checkpoint, not hard-target completion.

## WO-Q10.2 — verify tree-0 reconstruction repair

- [x] Read the handoff, COMMON rules, WO-2 spec, mailbox protocol, and campaign lessons.
- [x] Inspect the handed-off dirty diff and rebase `q10/wo2-verify-tree0` onto `8355fedc` with autostash.
- [x] Map all canonical tree-0 reconstruction calls and classify static versus candidate-count-dependent columns.
- [x] Capture the required release, one-thread before table: tree-0 reconstruction, Merkle verification,
      OODS/composition, and lookup/claimed-sum checks per hosted role.
- [x] Stop without a cache or commit restructuring per mailbox A-201: the cold LDE+Merkle cost is
      architecturally unreachable within the verify-side-only footprint.
- [x] Confirm the existing candidate-count, per-signature-root, forged-root, and statement-message negatives.
- [x] Capture the final exact production probe: tree-0 total, overall verify, proof bytes, and prove time.
- [x] Inspect the final documentation-only diff and commit locally without pushing.

### Review

Before attribution on `8355fedc`, release, production PCS, `RAYON_NUM_THREADS=1`:

| Phase | Time |
|---|---:|
| Issuer canonical columns | 5.69 ms |
| Device canonical columns | 5.78 ms |
| Revocation canonical columns | 5.96 ms |
| Shared Keccak-service canonical columns | 7.11 ms |
| Tree-0 twiddles | 2.50 ms |
| Tree-0 LDE + Merkle commit | 505.45 ms |
| Aggregate canonical tree-0 reconstruction | 541.35 ms |
| Verify setup + claimed sums | 8.11 ms |
| Stwo Merkle/OODS/composition checks | 9.50 ms |
| Residual STARK verify call | 17.61 ms |

The three ML-DSA instances each regenerate 104–105 columns, but only 5.69–5.96 ms per role
is attributable to canonical column generation. The 505.45 ms LDE+Merkle commit dominates.
Of each issuer/device role's 105 columns (revocation: 104), 48 protocol-static columns are
shared globally; the remaining 57 (revocation: 56) include namespaced ExpandA rejection,
SampleInBall, message, bridge, and sink schedules. ExpandA rejection content follows the
per-signature candidate-count vector, so a cold production verifier cannot amortize the root.
Mailbox A-201 therefore re-scoped WO-2 to attribution only and forbade a warm-only cache.

Final clean exact probe (`RAYON_NUM_THREADS=1 cargo run --release -p eu-id-prover --example
pq_perf_probe`): 24,961 ms prove, 568 ms verify, 1,199,150-byte proof, zero auxiliary
payload bytes. The expected prove rail misses; verify and proof-size also remain above the campaign
rails on this standalone branch. Four focused release negatives passed with one Rayon thread:
`mldsa_mdoc_reconstructs_tree0_and_gates_public_shape` (29.49 s),
`mldsa_mdoc_statement_message_tamper_rejects` (18.98 s),
`mldsa_mdoc_pin_is_per_signature_not_cached` (33.76 s), and
`mldsa_malformed_claim_tree_rejects` (19.33 s, including candidate-count tamper rejection).
All temporary mdoc/air-core timers were removed before the final diff.

## Milestone Q10 — post-Q9 performance campaign

- [x] Read the full Q10 handoff, COMMON rules, WO-1 through WO-5, mailbox protocol, and campaign lessons.
- [x] Rebase every `q10/wo*` branch onto `8355fedc` without pushing.
- [x] Complete and measure WO-1 (Keccak round-GKR offload), including the production-shaped
      ExpandA tamper and hosted missing-payload negatives authorized by mailbox A-100.
- [x] Complete and measure WO-2 as attribution-only per mailbox A-201; do not add a warm cache.
- [x] Re-verify and measure the WO-3 inverse-NTT spike before using it as design evidence.
- [x] Complete and measure WO-5 (coefficient range-relation split), including every required
      first-excluded-value boundary negative.
- [x] Integrate in the required WO-1 → WO-2 → WO-5 order and capture a clean exact frontier.
- [x] Implement the revised WO-4a accepted by mailbox A-404/A-405: one stacked log-15 butterfly
      component plus one log-13 scaling component, with no sumcheck payload or `air-core` change.
- [x] Run the combined release suite, strict clippy, diff/footprint checks, independent protocol
      review, and a final post-integration probe.
- [x] Record the missed prove rail without chasing it; do not push without approval.

### Q10 review

All exact product probes below use release mode, production `(4,26,25)` PCS, and
`RAYON_NUM_THREADS=1`.

| Work item | Measured result |
|---|---|
| WO-1 | 16,966 ms prove, 543 ms verify, 1,112,374 B proof, 21,864 B payload; 14,614,528 committed cells removed versus `8355fedc` |
| WO-2 | 541.35 ms canonical tree-0 reconstruction, including 505.45 ms LDE + Merkle; final standalone probe 24,961/568 ms and 1,199,150 B |
| WO-3 | 212.92 ms best-of-five for 30 inverse-NTT polynomials; 3,584 B payload; 652,800 arithmetic-cell model; GO as design evidence only |
| WO-5 | 20,198/520 ms and 1,171,638 B standalone; coefficient-provider model 5,024,448 → 2,949,120 cells (−2,075,328) |
| Pre-WO-4 integrated frontier | 18,026/548 ms, 1,083,950 B proof, 21,864 B payload |
| WO-4a | NTT model 6,029,312 → 2,940,928 cells (−3,088,384, −51.22%); 93.75% butterfly occupancy |

Mailbox A-402 retracted the proposed committed-intermediate sumcheck design. A first pure-AIR
eight-component split reached 2,908,160 NTT cells but enlarged the proof by about 216 KB, so A-404
replaced it with the stacked two-component shape above. The accepted claim order is rejection →
butterfly → scaling, and global `max_log_size` includes the new log-15 component.

The A-405 exact three-run final samples were:

| Run | Prove | Verify | Proof | Payload |
|---:|---:|---:|---:|---:|
| 1 | 17,180 ms | 437 ms | 1,097,142 B | 21,864 B |
| 2 | 14,166 ms | 436 ms | 1,099,606 B | 21,864 B |
| 3 | 14,473 ms | 436 ms | 1,096,390 B | 21,864 B |
| **Median** | **14,473 ms** | **436 ms** | **1,097,142 B** | **21,864 B** |

The official median improves the pre-WO-4 integrated frontier by 3,553 ms prove and 112 ms verify,
while adding 13,192 proof bytes. It passes the WO-4a acceptance caps (≤15,026 ms prove and no more
than 30 KB proof growth), but the campaign rails remain open: prove misses `<1,000 ms` by 13,473 ms,
verify misses `<100 ms` by 336 ms, and proof misses `<1,000,000 B` by 97,142 B. A final clean-tree
confirmation measured 14,215 ms prove, 453 ms verify, 1,096,774 B proof, and 21,864 B payload.

Final verification: all 181 active tests across `stwo-keccak`, `stwo-mldsa`, and `eu-id-prover`
passed in release mode (one documented composed benchmark ignored); strict all-target clippy passed
with warnings denied. Independent review reproduced the WO-4a census and found no soundness,
claim-layout, degree-bound, test-hook, or file-footprint issue. No branch was pushed.

## Firebase Android full-PQ benchmark

- [x] Confirm branch provenance, clean state, full-PQ fixture shape, and focused soundness gates.
- [x] Add the smallest benchmark-only JNI surface for the canonical full-PQ mdoc circuit:
      ML-DSA-65 issuer, device authentication, and revocation in one proof.
- [x] Reuse the existing Android Game Loop harness and emit an unambiguous full-PQ result schema.
- [x] Add focused tests for the benchmark fixture, failure handling, and result schema.
- [x] Run formatting, focused host tests, full-PQ release proof/verify, and strict clippy.
- [x] Build the release APK once, record its SHA-256 and embedded Git/Stwo provenance, and do not rebuild
      between Firebase executions.
- [x] Submit the exact APK to the established Firebase physical-device matrix and wait for all executions.
- [x] Download raw Game Loop artifacts, validate every proof result, and synthesize the device comparison
      under `tasks/bench-results/`.
- [x] Record commands, artifact hashes, matrix IDs, measurements, caveats, and final review here.

### Review

- Exact target: `feat/quantum-safe` at `d5c4ac980e81991374ecf88fdb8b47ef91cdeef4`;
  soundness hardening `e1896db1` is an ancestor and all four focused prior-failure/full-PQ
  release gates passed.
- Added one benchmark-only JNI entry point over the canonical full-PQ circuit. It proves
  ML-DSA-65 issuer + device authentication, age/nationality, and ML-DSA-65 TS13 revocation;
  verifies a public-only statement; forces a fresh tree-0 root before cached verification;
  and reports timing, raw proof size, lightweight peak RSS, and the effective Rayon count.
- Focused JNI/fixture tests passed (10 active, one slow ignored), the exact slow release FFI
  round trip passed, strict focused Clippy passed, and the independent review's sampler,
  public-statement, repeat-call, Game Loop failure, and labeling findings were fixed.
- Final APK SHA-256:
  `4a49ccf3638c4b13e4002e4ce555109fdbfa3c11ab25a3e59cc3dd0c2dd19473`;
  it is v2-signed, arm64-only, contains the Game Loop contract, and exports the required JNI symbol.
- Nine fresh physical-device processes passed with matching APK/Git/Stwo provenance and `ok=true`.
  Median prove / cold verify / warm verify: S24 Ultra `2,452 / 150 / 16 ms`; Pixel 8
  `3,084 / 282 / 23 ms`; A54 `4,591 / 261 / 32 ms`.
- Median raw proof is approximately 1.26 MB and median peak RSS is 622–641 MiB. The `<1 s`
  prove, `<100 ms` cold verify, and `<1,000,000 B` proof rails remain open; cached verify
  passes `<100 ms` on every device.
- Full report and all nine JSON artifacts:
  `tasks/bench-results/firebase-full-pq-mldsa-d5c4ac98/analysis.md`.
- Firebase matrices: `matrix-8nbff9k0kwrba`, `matrix-18br6gt5vorvd`,
  `matrix-17exhnj0y24q7`, and `matrix-2t7ab423iqwta`.

## Firebase Android full-PQ performance-core benchmark

- [x] Detect the process-allowed Android CPU topology, exclude the lowest-capacity cluster,
      and pin one dedicated Rayon worker to each remaining CPU.
- [x] Record the selected/excluded CPU IDs, topology source, actual worker count, and a distinct
      performance-core-only profile label in every result.
- [x] Run focused tests, the exact release round trip, strict Clippy, and APK inspection.
- [x] Run three fresh Firebase processes on A54, Pixel 8, and S24 Ultra.
- [x] Compare medians against the one-thread APK and classify the result
      correctly as an unpaired descriptive comparison.
- [x] Record the APK hash, matrix IDs, raw artifacts, measurements, and review.

### Review

- Android selected topology with `cpu_capacity` on every run and pinned only
  non-minimum-cluster CPUs: A54 `4-7` (4 workers), Pixel 8 `4-8` (5), and
  S24 Ultra `2-7` (6). The affinity startup handshake makes failure
  fail-closed rather than silently falling back to efficiency cores.
- Final APK SHA-256:
  `e6ffb2f6f3ebf11c448dcf6ef1294ca9c6d26d146e96ab3fa421da8509d763bb`.
  It is v2-signed, arm64-only, and was not rebuilt between any Firebase run.
- All nine fresh processes passed with stable device-specific CPU masks and
  matching APK/Git/Stwo provenance. Median prove / cold verify / warm verify:
  A54 `3,016 / 135 / 33 ms`; Pixel 8 `2,170 / 151 / 36 ms`; S24 Ultra
  `1,907 / 104 / 22 ms`.
- Versus the otherwise-equivalent one-thread campaign, the observed median
  differences are 34.3% on A54, 29.6% on Pixel 8, and 22.2% on S24 Ultra;
  median peak RSS differs by +9.8, +28.3, and +27.0 MiB respectively. These
  are unpaired campaigns using different APKs and unidentified Firebase units,
  so they do not establish a causal thread-policy speedup.
- The full-PQ hard rails remain open: prove and proof size fail on all devices,
  and cold verification medians remain just above 100 ms. Warm cached
  verification passes 100 ms on every sample.
- Independent read-only review found no release-blocking affinity,
  fail-closed, schema, or artifact-consistency issue.
- The 2026-07-23 double-check re-passed 108 active `stwo-mldsa` tests (one
  ignored), 30 SDK tests, 11 active FFI tests (one ignored), the exact release
  full-PQ FFI round trip, warnings-denied all-target/focused Clippy, and Android
  release assemble/lint. It also retained exact copies of both measured APKs
  and reconciled their packaged stripped native-library hashes.
- Full report and all nine JSON artifacts:
  `tasks/bench-results/firebase-full-pq-mldsa-bigcores-d5c4ac98/analysis.md`.
- Firebase matrices: `matrix-3nz2f9fdjljw4`, `matrix-3a19u6n95ow70`,
  `matrix-36djloxhx3pl9`, and `matrix-1bqd9g5yesl5k`.

## Quantum-safe Android SDK native-link failure

- [x] Resolve the user-named `feat/quantum-safe` branch to its owning worktree and preserve
      unrelated changes in the main checkout.
- [x] Trace the SDK compression dependency, Android AAR publication, wallet dependency
      resolution, and the exact native library currently packaged by the local wallet build.
- [x] Add the smallest Android build guard that rejects unresolved non-platform symbols in
      `libeuid_zk_sdk.so`.
- [x] Cross-compile the quantum-safe ARM64 SDK and prove that it has no zstd dependency or
      unresolved `ZSTD_*` symbols.
- [x] Republish the quantum-safe AAR locally, refresh the wallet dependency, and verify its
      merged ARM64 library is the new quantum-safe artifact.
- [ ] Migrate the consuming wallet from the classical `ZkWitness`/P-256 statement API to the
      quantum-safe `ZkMdocWitness`/ML-DSA API before producing a new final APK.
- [x] Record the root cause, artifact hashes, commands, and final review here.

### Review

- Root cause: `feat/android-bench` and `feat/quantum-safe` both publish
  `com.kss:eu-id-zk-sdk:0.1.0`. The wallet had packaged the zstd/classical branch's AAR while
  the current quantum-safe SDK uses `bzip2 -> libbz2-rs-sys` and has no zstd package at all.
  JNA found the APK library; its later resource-path errors were only fallback noise.
- Added `-Wl,--no-undefined` to both Android Cargo targets so a missing native dependency fails
  the SDK link rather than on-device `dlopen()`. Cargo fingerprints confirm the flag reached
  both targets. The NDK remains pinned to 30 by default but can now be selected explicitly with
  `-PndkVersion=...`; local verification used the installed `27.1.12297006`.
- Updated the Android instrumented smoke test to the current `IssuerKey.MlDsa` and
  `TrustedIssuers.PublicKeys` UniFFI types. `cargo test -p sdk --lib` passed all 30 tests;
  `assembleRelease`, `assembleAndroidTest`, and `lintRelease` all passed.
- Published AAR SHA-256:
  `4e6714c90f30112cc4680f5af433558f9459cb3d5e43bd20b8207fd858a092ef`.
  Its unstripped ARM64 library is
  `67170a5b9d01cce48b95111deb7abb695f2605e7b6a4292a50f489e7b5164a79`;
  the packaged/stripped ARM64 library is
  `cf71323e5e6d467fba12951c1a4d9318d2e7c9b7730d9b2e2e72baedb50e48dc`.
- `llvm-nm -D -u` on the published and wallet-merged ARM64 libraries contains no `ZSTD_*`
  symbol. `llvm-readelf -d` reports only `libdl.so` and `libc.so`. The refreshed wallet merge
  contains the exact packaged hash `cf7132...`, proving the bad native artifact was replaced.
- The final wallet APK is not rebuilt yet: refreshed Kotlin compilation correctly rejects the
  old classical consumer source (`ZkWitness`, `issuerKeyX`, `issuerKeyY`) against the quantum
  API (`ZkMdocWitness`, `IssuerKey.MlDsa`). That migration belongs in
  `/Users/lucas/profiling/eudi-zk-android-wallet`; no source there was modified.

## WO-S2 + WO-C1 implementation on feat/quantum-safe

- [x] Verify the target worktree is `feat/quantum-safe` at `c5145004`, read both work orders,
      COMMON.md, the mailbox protocol, and the existing campaign lessons.
- [x] Capture the pre-change AIR shape census and establish focused test baselines.
- [x] Implement WO-S2 in order: boundary fixes, circuit/product/TS13 negatives, then hygiene.
- [x] Implement WO-C1 in order C1-C7, preserving relation order, AIR shape, pins, and negative
      coverage; resolve the gated `expand_a.rs` deletion through the mailbox.
- [x] Run every phase's focused release tests, then the full touched-crate/workspace acceptance
      suite with `RAYON_NUM_THREADS=1`.
- [x] Re-run the AIR census and performance probe, compare the census byte-for-byte, review the
      complete diff, and record measured numbers.
- [x] Commit only the WO-S2/WO-C1 implementation on `feat/quantum-safe`, preserving the unrelated
      Android and pre-existing task-tracking edits.

### Review

- A-719 mailbox resolved by `A-726`: prove-side acceptance is not the forgery signal because the
  private-window binding is cross-component LogUp; verifier global claimed-sum cancellation is the
  soundness boundary. The regression now proves an honest control, proves the consistently moved
  statement, and asserts `eu_id_prover::verify_mdoc` rejects outside host validation.
- WO-S2 safe scope completed: SDK demo code is gated behind the `demo` feature; the TS13 verifier
  runs on `on_large_stack`; product identity and TS13 real-proof/tampered-STARK negatives pass;
  `mldsa_range_table_claimed_sum` is crate-private with test hooks; `prepare_mldsa_role` now
  asserts it does not overwrite a non-default `tr`.
- WO-C1 C1-C7 safe scope completed: removed gkr-spike, deleted vestigial SHA decode/Maj/Ch/xor_8
  committed-table machinery, cleaned dead ML-DSA modules/items and duplicated helpers, retired the
  standalone keccak test prover after porting service-path coverage, removed predicate
  bit-decomposition strategy code and air-core dead utilities, then swept stale active-source
  comments.
- Mailbox-gated items resolved and applied: `A-723` approved deleting abandoned
  `crates/stwo-mldsa/src/expand_a.rs`; `A-724` approved fail-closed product rejection for
  revocation-bearing statements and one-line docs; `A-725` approved top-level Makefile and
  predicate usage-doc removal of deleted bit-decomposition commands.
- Verification run: `cargo build -p sdk`; `cargo test -p sdk --features demo --lib`;
  release `product_identity_e2e`, `ts13_e2e`, full `eu-id-prover --test mdoc_mldsa`,
  `eu-id-ffi`, `stwo-keccak`, `stwo-mldsa`, and final release bundle
  `stwo-sha256 stwo-mldsa predicates air-core`.
- Final AIR check: `/private/tmp/wo-c1-census-before.log` vs
  `/private/tmp/wo-c1-census-final-after-mailbox.log` has byte-identical `air-core shape` lines
  (`42 == 42`). Final probe:
  `PQ_PERF_PROBE rayon_threads=1 prove_ms=1173 cold_verify_ms=107 cold_tree0_root_ms=91
  cold_stark_verify_ms=16 warm_verify_ms=15 warm_tree0_root_ms=0 warm_stark_verify_ms=15
  proof_bytes=1265795`.

## Unlinkability campaign implementation (2026-07-29)

Branch/worktree: `codex/unlinkability` at
`/Users/lucas/eu-id/.claude/worktrees/codex-unlinkability`, created from the
exact `feat/quantum-safe` HEAD `abf9c27f32bc857f6de7994cfca7ab9372e43baa`.

### Plan

- [x] Import the authoritative unlinkability work orders into this isolated
      worktree, reconcile their `41530e51+working-tree` scope with current
      branch history, and record the mailbox convention.
- [x] Implement WO-U0a as an example-local private-message issuer spike;
      prove and verify completeness, then record three cold process
      measurements and Keccak/round shape.
- [x] Implement WO-U0b as an example-local Keccak scaling spike; record cold
      37/100/202-permutation measurements and enforce the STOP/GO budget.
- [x] Resolve the U0b STOP/replan gate through `A-727`, land the exact
      `4f39939e` four-family repin as a two-file commit, and reproduce the full
      post-repin test/parity/performance/demo acceptance matrix.
- [x] Append the witness-offset constraint design and the U1/U2/U4 sequencing,
      digest-ID, and compatibility-cut questions to the mailbox.
- [x] Obtain mailbox approval for Q-728 through Q-731 and fold every additive
      range, same-cell, versioning, tree-0, polarity, anchor, and µ-totality
      condition into the authoritative constraint addendum.
- [x] Implement the approved Phase-1 pair with its full proof-level negative
      matrix, product/TS13 e2e gates, wire byte-grep privacy gates, identical
      public-shape tree-0 regression, and three cold measurements.
  - [x] Land the dynamic private issuer-message provider and fixed-width
        padded-MSO SHA stream exposure with independent component tests.
  - [x] Prove the private issuer-message provider's exact relation contract:
        every byte index balances one µ consumer plus its declared extra uses,
        ±1 is checked algebraically at every position, representative
        missing/extra proofs reject at global LogUp, and the maximum
        non-wrapping M31 multiplicity is pinned.
  - [x] Prove the private MSO binder's issuer/SHA/start relation seams under
        the production PCS config; correct its paired-LogUp degree budget from
        `log+1` to cubic `log+2`, retain coefficients, and reject eight
        counterpart mutations at the global balance check.
  - [x] Keep the MSO issuer relation denominator linear: pin the active
        payload-anchor `window_offset` to zero, remove the selector×offset
        product, symbolically pin the degree, and verify both production and
        minimum-blowup composed proofs.
  - [x] Prove the private item binder's five relation seams under the production
        PCS config; correct its paired-LogUp degree budget from `log+1` to cubic
        `log+2`, retain coefficients, and reject one counterpart mutation per
        relation family at the global balance check.
  - [x] Retain CBOR parser polynomial coefficients and prove/verify a balanced
        private-provider/parser composition under the default minimum-blowup
        PCS configuration.
  - [x] Reject malformed public shape before SHA/layout/tree-zero/module
        construction: attributes 1..=4, 32-byte identifier/equality caps,
        issuer/device/MSO/docType caps, policy date, and TS13 public
        reconstruction all return phase-typed errors without panicking.
  - [x] Re-land A-728/A-731's constant-width private-MSO SHA stream with fresh
        A-740 Phase-1 provenance in `362743af`; 165 normal and 18 ignored SHA
        tests plus namespace, collision, and stream gates pass.
  - [x] Land the private MSO binder, complete tdate/profile/device binds, and
        A-732's 324-column fixed-log-9 canonical multi-namespace scanner with
        exact provider multiplicities, typed compatibility errors, the full
        proof-negative matrix, and all available real-vector checks.
  - [x] Apply A-738's product-v1 token-language cut: require
        minimal/definite/exact IssuerSignedItem CBOR with no trailing data,
        preserve v1 key order and value forms, bound the tag-24 outer prefix,
        and return typed token+offset errors before proof construction.
  - [x] Make each private digest ID one canonical witness across item and MSO
        surfaces; chain A-734's private `is_v2` bit through the same
        `(mso_start,is_v2)` and selected-digest tuples; remove public digest
        binds and credential-derived preprocessing/transcript inputs.
  - [x] Delete the provisional verifier dependence on
        `check_mldsa_device_key_binding`/`mldsa_public_mso_facts`, remove
        `PublicDigestBind` and the old equality-scope path, and construct the
        issuer provider only after binder+scanner use censuses are frozen.
  - [x] Integrate private issuer mode, conditional revocation MSO SHA, and
        decoupled revocation-message polarity in identical prove/verify order.
  - [x] Namespace the conditional standalone MSO-SHA consumer without
        changing legacy SHA IDs/transcripts, so its log-13 preprocessing
        coexists with the smaller merged attribute SHA instead of colliding.
  - [x] Retire the superseded U0a private-message spike and its dead field
        producer after production adopted private issuer messages; collapse
        the revocation range AIR to its sole live private-digest relation mode
        and stop synthesizing an ignored verifier-side revocation signature.
  - [x] Freeze the layout, then apply A-730's single V7/V3/v10/cache-v5 cut,
        include the canonical issuer docType byte length in the cache key, prove
        fresh/memoized roots agree across differing lengths, and republish the
        TS13 caps/hash in one commit.
  - [x] Run the complete Phase-1 positive/negative/privacy/cache/performance
        gate before proceeding to the remaining U3/U4 sweep.
- [x] Implement U3's public-statement fingerprint scrub and U4's in-circuit
      revocation-id derivation after appending U4's constraint/cost design.
  - [x] Close reduced U4's public-exposure gate: document epoch partitioning,
        keep the revocation id/endpoints/digest/signature out of the clear TS13
        statement, and record that A-741 puts masking out of scope, so no
        endpoint-indistinguishability claim is made.
  - [x] Remove the redundant serialized age/nationality attribute indices and
        their tree-zero cache members; derive both positions from the ordered
        public attribute modes and keep the SDK's identifier+mode list
        authoritative.
  - [x] Delete the dead test-only `Ts13MdocProofArtifact` path that bypassed
        the pinned TS13 verifier; retain the real SDK public-envelope path as
        the single red-to-green Phase-1 integration gate.
  - [x] Implement A-735's fixed maximal private predicate normalization:
        packed/text/tag-1004 dates and numeric/alpha-2/scalar/array
        nationalities produce one public request-mode shape; pin celes 2.8.2,
        exact 250+XK mapping, full negative matrix, uncached equal-root gate,
        and measured cells/prove time.
  - [x] Implement A-736's exact two-entry Phase-1 fingerprint whitelist
        (device key and permanent issuer trust key), an ignored Phase-2
        empty-whitelist/device-key-run gate, and no serialized `valid_today`
        field.
  - [x] Zero/clear the 24 dead credential-derived legacy fields in the current
        public projection, keep `mso_payload_len`, and clear the TS13-only item
        bucket on product envelopes; physically remove the fields in the
        single A-730 version/layout cut.
- [x] Append the U5 rejection-sampler constraint, width, six-block cap, and
      transcript design after main-loop review.
- [x] Close the independent U5 audit findings before Phase-2 integration:
      pin tree zero in proof tests, finish the frozen negative/host-validator
      matrix, reject invalid stream bases without wrap/panic, and retain named
      ignored proof/service acceptance gates.
- [x] Phase 2 is deferred by A-733. Do not implement U5/U6/U7/U9 until a
      separate authorization; record the clean NTT path as presumptive,
      invalidate the old 1–1.5 s estimate, and preserve the canonical
      unscaled coefficient-domain `T1Cell(i,m,lo9,hi1)` producer contract.
  - [x] Append U9's fixed-log-9 canonical FIPS packed-key decoder, private
        MSO-start bridge, exact range census, relation polarity, and negative
        matrix; keep its `T1Cell` dependency explicit in Q-733.
  - [x] Append U7's private-pk `tr` plus mandatory private-µ Keccak wiring,
        exact claim/layout delta, normalized U9 byte bridge, wire projection,
        module order, and adversarial matrix.
  - [x] Land and independently exercise U7's hosted-private-key core mode:
        four service jobs, field-id-1 `pkEncode` bridge, key-independent
        public mix, exact 20-claim/layout API, and wrong-key/shape negatives.
  - [x] Make the new hosted-private-key verifier constructor reject short or
        long group-evaluation/claim vectors before the legacy
        `Claims::from_flat` panic boundary; add all four malformed-shape tests.
  - [x] Resolve Q-739 by creating
        `parked/unlinkability-phase2-u5-u7` at `81946a21`; retain only the
        U5/U7 commits there, with no integration authorization.
  - [x] Drop `0e60a4d3`, `81946a21`, and `bf1deb32` from Phase-1 history.
        A-740 corrected `bf1deb32` as mandatory A-728/A-731 Phase-1
        infrastructure; re-land its active SHA stream support with fresh
        provenance while keeping only U5/U7 parked.
  - [x] Verify the final Phase-1 delivery from a fresh checkout has no U5/U7
        exports/features/files and keep their evidence out of Phase-1
        acceptance. The clean post-drop checkpoint passed 54 stwo-mldsa and
        146 stwo-sha256 tests; eu-id-prover exposed the known incomplete
        Phase-1 checkpoint and must be repeated after the integrated commit.
- [x] After mailbox authorization, pin the exact already-pushed Stwo GKR
      parallel candidate `4f39939e` and rerun all gates. The permanent pin
      closes U0b at +462/+545/+471 ms, so the full permutation-chain U8 is
      skipped unless a later Phase-2 gate reactivates it.
- [x] Close Phase 3 as out of scope under A-741, which supersedes A-737:
      produce no ZK design/worksheet, request no ZK Math Review, make no Stwo
      proof-system edit, and perform no ZK measurement or forward planning.
  - [x] Create a clean `codex/unlinkability-zk` Stwo fork checkout at the
        exact pinned `4f39939e` revision without touching the user's dirty
        `/Users/lucas/stwo` checkout.
  - [x] Record A-741's final release boundary: `ZK=false`, no ZK or
        unlinkability claim, and post-quantum issuer + holder authentication
        with selective disclosure only.
- [x] Run release-optimized, one-Rayon-worker workspace shards, the ignored prover
      suite, formatting/lint policy, all named privacy/soundness gates, and
      final cold performance measurements; update the demo-prep table with
      V7/V3 results before any landing onto a demo-quoted branch; review the
      complete diff and fill in this section's Review.

### Review

- Phase-0 probes live behind the default-off `eu-id-prover/unlink-spikes`
  feature. Default builds exclude the spike AIR and hidden APIs, retain the
  production inner entrypoint shape, and serialize the byte-identical v4
  tree-0 cache material. Feature/default checks and cache-key tests pass.
- U0a completes and verifies from a serialized+Bzip2-round-tripped proof,
  rejects production public-message verification, and measures 674–696 ms
  prove across three cold 12-thread processes for 55 total Keccak
  permutations. Its issuer message is 2,294 bytes; the measured rail passes
  the 1.2 s gate.
- U0b completes and verifies at all three points and rejects a same-proof
  verifier configured for a different dummy-job count. Both probes now use a
  named local Rayon pool with 32 MiB per worker after an outer-thread-only
  diagnostic exposed an intermittent worker-stack overflow. The stack-safe
  cold 12-thread point-202 prove time is 1,505–1,544 ms versus 523–530 ms at
  point 37: paired overhead is 976–1,014 ms, exceeding the 700 ms hard budget.
- Work therefore stopped before Phase 1. Watched mailbox question
  `Q-727-unlinkability-u0-stop-go.md` requests the required replan decision.
  Read-only U8 reconnaissance first attributes 7,992,320 of the 10,062,720
  point-37→202 marginal service cells to the committed Keccak-round trace, but
  finer timers localize the immediate scaling fault to the existing
  lookup-GKR prover: `prove_batch` grows from 87.7 ms to 663.9–719.8 ms while
  actual component/tie-back generation remains below 1.4 ms. The current pin
  leaves those SIMD kernels sequential; already-pushed fork revision
  `4f39939e` parallelizes them and carries CPU/SIMD proof-parity tests without
  verifier or proof-format edits. A clean reversible A/B measured point 37 at
  463–481 ms and point 202 at 966–997 ms, giving paired overheads of
  +523/+485/+505 ms; encoded transcript equality, serial/parallel parity, and
  stable-digest tests pass. The override was removed and the pins restored.
  The mailbox question now requests the exact permanent repin; if approved,
  the original full-transition U8 is unnecessary under its own cost gate.
- Blocking audit: three consecutive goal turns found no `A-727` response
  after bounded watches and direct outbox checks. Phase 1 and the permanent
  four-pin change remain paused rather than silently overriding the
  cross-repository authorization rule.
- `A-727` subsequently authorized the exact repin. Commit
  `821d8c7d967043678d0c7486a40377937d0b06bc` contains only the four manifest
  revisions and four matching lockfile sources; the lock graph has no
  transitive or `hashbrown` drift. Default workspace, `unlink-spikes`
  workspace, all ignored gates, consumer encoded-GKR equality, exact-pin
  CPU/SIMD GKR+MLE parity, and serial/parallel stable-digest checks all pass.
- Permanent-pin cold U0b pairs are +462/+545/+471 ms (all below +700), the
  one-worker point-202 result is 2,853 ms versus the old 2,914 ms, and U0a is
  542/561/607 ms. Product demo prove improves to 507–513 ms and TS13 to
  487–500 ms; the full named results are recorded in both campaign reports.
- Phase 1 is GO, but read-only implementation mapping found two
  soundness/spec sequencing conflicts that must be resolved before U2: TS13
  loses its public MSO digest before U4 supplies an in-circuit replacement,
  and U2's no-digestID wire gate conflicts with U3 owning the digestID move.
  Q-728 through Q-730 request those sequencing and compatibility rulings.
  Q-731 submits the degree-2 row-wise provider/binder design, common
  payload-anchor and range proof, full padded-stream SHA bridge, complete tdate
  and profile-constant binds, namespace-scope decision, and corrected capacity
  census. A-728 approves pulling the range-exact private-MSO SHA/revocation
  bridge into Phase 1; A-729 approves pulling digest-ID privacy into the pair
  with one committed ID/canonical encoding consumed on both signed surfaces.
  A-730 approves the one post-layout V7/V3/v10/cache-v5 compatibility cut and
  makes credential-independent tree-0 roots a gate. A-731 approves the U2
  design with an explicit polarity table, honest-fixture anchor negative, and
  exhaustive issuer µ-consumer test. Phase-1 implementation is authorized;
  Q-732 now asks the one remaining compatibility-specific choice: the exact
  bounded multi-namespace valueDigests scan instead of an unapproved
  single-namespace narrowing.
- Phase-2 exact-domain review found that U5 emits NTT-domain `Â` while the
  current folded identity consumes coefficient-domain `A`. Q-733 asks whether
  to restore the historical stacked inverse-NTT AIR or use a separately
  approved NTT-domain identity; direct Horner substitution is forbidden.
- The requested `air-writer` skill was unavailable in this Codex session.
  Phase-0 relation signs, degree bounds, module order, and claim shapes were
  instead derived from and cross-checked against the existing hosted-message
  and Keccak-service AIR implementations; this deviation is also recorded in
  the authoritative work-order report.
- U5's two claimed sums now have an explicit serialized proof-claim type and
  an exact bincode round-trip regression, ready for composed-proof wiring.
- U6 now has two complete in-repo domain designs with exact signs, bounds,
  claims, tree timing, and cell censuses. Q-733 selects between the audited
  inverse path and the 655,360-cell-smaller clean NTT-domain refactor before
  either implementation begins.
- The full product statement serialization regression now proves that private
  issuer bytes, both authentication signature witnesses, the revocation
  signature, and revocation gap endpoints are absent; deserialization
  reconstructs only verifier-safe placeholders.
- The follow-up dead-path sweep removed the superseded U0a
  example/configuration and the unreachable issuer-field half of the remaining
  U0b Keccak probe. It also collapsed `MdocRevocationRangeBind` to its sole
  live private-digest relation mode without changing the 336 trace-column /
  48 interaction-M31-column geometry, and stopped verifier reconstruction from
  allocating an ignored zero revocation signature. Focused release projection,
  geometry, and provider-message tamper tests pass.
- The broad fully-PQ e2e was deliberately not treated as green: proving
  completes, then the test's first legacy direct verification passes the
  original prover-side statement and is rejected by the public-auth projection
  guard. This is the recorded Phase-1 integration boundary, not a reason to
  weaken the guard; the test moves to the final public statement only after
  Q-732/Q-734/Q-735/Q-738 close the missing scanner/item links.
- The same boundary is now confirmed through the production SDK path:
  `ts13_equality_envelope_proves_and_verifies_with_public_only_envelope`
  builds a real proof but returns `false` on public-only verification because
  `check_mldsa_device_key_binding` and `mldsa_public_mso_facts` still parse the
  intentionally zero-projected issuer message. Static review also found the
  private MSO binder's negative `MdocMsoStartRelation` tuple has no scanner
  consumer and the private item binder is not yet in the production
  composition. Those fail-closed blockers remain red until the pending
  scanner/version/predicate/CBOR rulings land.
- The issuer provider now has a real two-module STARK control rather than only
  row/claim-delta tests. One use at every index `0..37` verifies; missing
  first/middle/last and extra-middle use proofs reject specifically because
  the global LogUp sums do not cancel, while the paired algebraic test checks
  ±1 at every position. The full private-message module reports 8/8.
  The final composition must repeat this totality check against the actual
  hosted ML-DSA µ bridge, not just the faithful test consumer.
- The analogous six-column MSO test counter exposed a real completeness bug:
  the binder paired two live denominators while reporting a degree-2 bound.
  A follow-up degree census found that the old masked issuer index would make
  two issuer denominators quartic and the recurrence quintic. Instead of
  raising the budget to `log+3`, the active payload-anchor row now constrains
  `window_offset=0` and the shared AIR/packed relation key adds that offset
  linearly. A symbolic degree regression pins the construction; production
  and minimum-blowup composed proofs verify. Shifted anchor/start, raw MSO,
  three SHA padding seams, and missing/extra start uses reject at the exact
  global LogUp check. The binder retains coefficients and the exact `log+2`
  budget without adding a column or changing claims, layout, tree zero, or
  transcript fields; its focused release module reports 13/13.
- The private item binder had the same underreported paired-LogUp degree:
  consecutive trace-linear denominators make the accumulator identity cubic.
  Its evaluator and prover now report `log+2` and retain coefficients. A
  compact five-family counter balances `item_fields`, both parsed-CBOR
  relations, `inner_raw`, and the private digest-ID handoff. The honest
  production-PCS proof verifies, and one tuple mutation in every family
  rejects at the exact global LogUp check. The focused release module reports
  17/17; the planned Phase-1 compatibility cut already owns the changed
  constraint identity.
- The degree-seven CBOR parser now independently requests polynomial
  coefficient retention instead of relying on another composed module to do
  so. A real private-message-provider/parser proof verifies under default
  minimum blowup. The combined release prover library reports 65/65, the
  release SDK library remains 29/29, and `unlink-spikes` examples check
  cleanly. Independent degree/sign/layout reviews found no outstanding P0–P3
  issue across the MSO, item, and CBOR repairs.
- Final Phase-1 composition replaces every provisional host/public digest
  path with the private provider → strict CBOR item binders → country
  normalization → canonical multi-namespace valueDigests scanner → private
  MSO binder chain. Provider multiplicities are checked-added from the frozen
  binder/scanner censuses before the issuer ML-DSA module is constructed;
  prover and verifier module order is identical. V7/V3/v10/cache-v5 is the
  sole accepted wire/layout tuple.
- The final release matrix is green: 99 prover-library, 27 mdoc integration,
  101 `unlink-spikes` feature-library, 165+18 ignored SHA, 110+1 ignored
  ML-DSA, 34 Keccak, 66 predicates, 18 Air Core, 33 SDK-library, 7 product
  e2e, 7 TS13 e2e, and 2 FFI tests. Release all-target check, strict
  all-target Clippy with warnings denied, formatting, and whitespace checks
  pass. The intentionally red ignored U9 empty-device-key gates remain
  deferred Phase-2 acceptance tests.
- Three cold 12-core release runs report Phase-1 TS13 core prove
  742/769/759 ms, fresh verify 48/49/42 ms, raw proof
  1,552,867/1,557,427/1,555,443 bytes, and Bzip2 wire
  1,213,977/1,220,424/1,217,117 bytes. The 2,513-byte realistic MSO pads to
  `phase1_revocation_sha_rows=2560` (40 blocks). Median Phase-1 core minus the
  U0a median gives the conservative, whole-bridge upper bound
  `phase1_revocation_sha_ms<=198`; it includes scanner/binder/normalization
  work and therefore does not misrepresent that bound as isolated SHA time.
  `u3_normalization_prove_ms=52` is the median of 15 one-worker release
  composed proofs.
- Product SDK cold prove is 609/615/627 ms, verify 85/86/86 ms, with median
  `phase1_envelope_bytes=1,247,593`. TS13 SDK cold prove is 851/887/847 ms,
  first verify 93/94/95 ms, and median document wire 1,229,490 bytes. The core
  maximum 769 ms remains below the work-order's 789 ms worst-case U0a×1.3
  ceiling.
- The three-envelope U3 regression proves that normalized public regions and
  tree zero are credential-independent, applies the exact two-entry Phase-1
  whitelist, and rejects raw MSO/high-digest-ID/timestamp/Sig_structure/
  signature/private-attribute markers in both wire and decompressed proof.
  A genuinely different same-public-shape credential has the same fresh and
  memoized tree-zero root.
- Phase 1 is not unlinkable by itself: the 1,952-byte device public key
  remains a credential-stable public value, so presentations of the same
  credential remain linkable by that key. The profile also remains
  `zero_knowledge=false`. A-733 keeps U5/U6/U7/U9 absent from this delivery,
  and A-741 removes Phase 3/ZK entirely from scope.
