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

- [ ] Format all changed Rust and Kotlin files.
- [ ] Pass release workspace check for all targets.
- [ ] Pass release Clippy with warnings denied.
- [ ] Pass release unit and integration tests.
- [ ] Pass focused `proveIdentity` and `verifyIdentity` envelope tests.
- [ ] Regenerate the source-bound circuit artifact and hash.
- [ ] Record the canonical circuit geometry and envelope capacity.
- [ ] Update the Android fixture with the new circuit hash.
- [ ] Build and test the canonical Android binding.
- [ ] Pass `git diff --check`.

## Invariants

- Keep the fixed TS13 theorem and identity-proof envelope.
- Keep the credential-independent public-input surface.
- Keep one ISO MSO 1.0 circuit path.
- Accept valid `IssuerSignedItem` map-key permutations.
- Keep `proveIdentity` and `verifyIdentity` as the only application API.
- Do not add STWO masking or performance work in this cleanup.
- Regenerate the circuit hash after all source cleanup.

## Review

Complete this section after all verification passes.
