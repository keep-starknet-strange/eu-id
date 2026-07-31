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
- [x] Remove or derive unnecessary preprocessed columns.
- [ ] Regenerate the circuit artifact and update its geometry records.
- [ ] Run the complete release verification after the audit fixes.

## Invariants

- Keep the fixed TS13 theorem and identity-proof envelope.
- Keep the credential-independent public-input surface.
- Keep one ISO MSO 1.0 circuit path.
- Accept valid `IssuerSignedItem` map-key permutations.
- Keep `proveIdentity` and `verifyIdentity` as the only application API.
- Do not add STWO masking or performance work in this cleanup.
- Regenerate the circuit hash after all source cleanup.

## Review

The final source-bound artifact check passed after all generated build files moved out of the
soundness source roots.

- Soundness source commit: `2d46ab7072d3f1ccbeba1d94d2bf867632e1c06a`.
- Soundness source-tree SHA-256: `374693d509c77303a3d3913394aae900262fb833886b5ea46f1d56d2792a666c`.
- Normative specification SHA-256: `01606b356cad9101da23a71fd8de537c5616f9430b856d09aa3101da81916060`.
- `Cargo.lock` SHA-256: `9c4615255aa28e4d2dd46263a6cf1b2c4f2b82129453d955ae871bc8d8c529fb`.
- Rust toolchain: `rustc 1.94.0-nightly (86a49fd71 2026-01-14)`.
- Circuit SHA-256: `4134801384833ac572475617ce6f05637f0d7f5b5d1fb868d9b3df9b653342d1`.
- Shape-manifest SHA-256: `bf67ed51c1bcde99811b13d72fdf8ea260b01f5f318f39adbe00c57f936241aa`.
- Merkle-tree column counts: `[946, 4906, 2400, 8, 32]`.
- Query count: `36`.
- Sampled secure fields: `10,709`.
- Serialized non-STARK claims: `24,136` bytes.
- Outer claims and framing: `3,840` bytes.
- Deterministic maximum proof body: `1,734,952` bytes.
- Pinned proof-body capacity: `1,769,472` bytes.
- Fixed envelope size: `1,769,518` bytes.

Release verification used `RAYON_NUM_THREADS=12`, `RUST_MIN_STACK=536870912`, 12 Cargo jobs,
and one test-harness thread.

- The all-target workspace check passed.
- Clippy passed for all release targets with warnings denied.
- The main workspace run passed 467 tests and left 18 ignored tests.
- The ignored-test run passed all 18 tests.
- The complete composed proof and all three TS13 integration tests passed.
- The SDK identity-envelope and unlinkability tests passed.
- `cargo fmt --all -- --check` and `git diff --check` passed.
- The artifact drift check passed with the circuit hash above.

The Android release build completed for `arm64-v8a` and `x86_64`. The demo release APK and its
release instrumentation APK also compiled. No device benchmark ran because performance work is
deferred.

- SDK AAR SHA-256: `ef0204fe0ca350f46a8e2c9e45c11490f0c61f7704fd284b5e19c6ef72ab575a`.
- Demo APK SHA-256: `4905cb677e74795a293b7fc47b565fabba15a84eaece06df792558c770c6b484`.
- Instrumentation APK SHA-256: `981e146e5e50aa1e0b0e81f2aeec8a46249d8c0d140593bb0036561907eea3eb`.

The demo provides public-input unlinkability. STWO transcript zero knowledge is pending and is not
part of this implementation.
