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
