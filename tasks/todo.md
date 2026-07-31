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
- [ ] Regenerate the circuit artifact and update its geometry records.
- [ ] Run the complete release verification after the audit fixes.

## Performance campaign

- [x] P0: Add or verify phase timing and peak-memory measurements.
- [ ] P0: Run the current canonical `proveIdentity` Firebase baseline.
- [ ] P1: Measure canonical-path overhead against the proof core.
- [ ] P2: Measure Keccak cell and prover-cost reductions.
- [ ] P3: Profile SHA and record redesign candidates without weakening the theorem.
- [ ] P4: Sweep safe FRI configurations within the proof-envelope limit.
- [ ] P5: Measure mobile worker counts, CPU selection, SIMD use, and peak RSS.
- [ ] P6: Run only if the primary-device target still needs another architectural change.
- [ ] Record cold and warm latency, proof size, peak RSS, source revision, and device metadata.

## Invariants

- Keep the fixed TS13 theorem and identity-proof envelope.
- Keep the credential-independent public-input surface.
- Keep one ISO MSO 1.0 circuit path.
- Accept valid `IssuerSignedItem` map-key permutations.
- Keep `proveIdentity` and `verifyIdentity` as the only application API.
- Do not add STWO transcript masking in this campaign.
- Benchmark only the final soundness-checked artifact and canonical `proveIdentity` path.
- Regenerate the circuit hash after all source cleanup.

## Review

The source audit is complete. The final artifact, release matrix, and benchmark evidence are in
progress. This implementation provides public-input unlinkability. STWO transcript zero knowledge
is pending and is not part of this campaign.
