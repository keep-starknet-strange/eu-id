# Q-001 — Phase 0b sizing waste route

Date: 2026-07-03
Status: answered
Phase: mdoc Phase 0b
Blocking: yes

Phase 0b asks to remove two known waste sources if possible:

1. Replace `prove_mdoc_circuit`'s shared `shared_sha_log = max(...)` padding
   with per-instance SHA log sizes.
2. Drop the mdoc device P256 `.with_preprocessed_namespace("mdoc/device")`.

Both direct trials fail the slow proof, so I restored the known-good code and am
asking before taking a larger refactor.

## SHA trial

Changed the four mdoc SHA modules to use their natural sizes:

- issuer SHA: `issuer_sha_log`
- device SHA: `device_sha_log`
- birth-date item SHA: `birth_sha_log`
- nationality item SHA: `nat_sha_log`

Then ran:

```bash
rtk proxy cargo test -p eu-id-prover --test mdoc_support isolated_mdoc_circuit_profile_proves_and_verifies --release -- --ignored
```

Result:

```text
mdoc circuit proves: Prove("ConstraintsNotSatisfied")
```

I restored the known-good `shared_sha_log` path after the failed trial.

### Likely cause

SHA preprocessed columns are keyed by stable IDs and deduped globally. Most SHA
lookup tables are static, but at least the `is_first_row` selector and the
round-cyclic columns are sized by `log_n_rows`. With four SHA instances using
different `log_n_rows`, the shared IDs no longer describe identical
preprocessed columns.

### SHA options

1. Keep `shared_sha_log` for Phase 0b.
   - Cost: zero implementation risk.
   - Downside: keeps the known row waste and weakens the Phase 0b perf goal.

2. Split SHA preprocessed IDs into static shared IDs plus log-size-sensitive IDs.
   - Cost: medium. Requires changing SHA preprocessed ID generation, selected
     preprocessed writing, verifier layout, and tests so only truly identical
     columns dedupe globally.
   - Upside: preserves four independent SHA modules while letting small item
     preimages use small traces.

3. Build one multi-message SHA module for the four mdoc preimages.
   - Cost: high. Requires a new witness/layout surface for multiple independent
     messages and multiple digest/field exposures from one SHA module.
   - Upside: can amortize static tables and scheduling cleanly, but it is not a
     one-day patch.

## P256 namespace trial

Removed `.with_preprocessed_namespace("mdoc/device")` from:

- the mdoc shape helper,
- the device P256 prover in `prove_mdoc_circuit`,
- the device P256 verifier in `verify_mdoc_circuit`.

Then ran:

```bash
rtk proxy cargo test -p eu-id-prover --test mdoc_support isolated_mdoc_circuit_profile_proves_and_verifies --release -- --ignored
```

Result:

```text
mdoc circuit proves: Prove("ConstraintsNotSatisfied")
```

I restored the namespace after the failed trial.

### P256 likely cause

The device and issuer P256 drafts have different witness-dependent hinted-mul
schedules. The previous isolated mdoc work already found that repeated P256
instances need namespace separation for witness-dependent preprocessed columns.
The main monolith's nonce path sharing does not imply these two mdoc signatures
share the same schedule.

### P256 options

1. Keep `mdoc/device` namespace.
   - Cost: zero implementation risk.
   - Downside: keeps duplicate preprocessed schedule columns.

2. Split P256 preprocessed IDs into deterministic shared IDs and
   witness-dependent schedule IDs.
   - Cost: medium/high. Requires auditing every P256 preprocessed column,
     namespacing only witness-dependent schedules, and updating layout/config
     paths.
   - Upside: recovers safe deduping where valid without aliasing schedules.

3. Force identical schedule shape for issuer/device P256 drafts.
   - Cost/risk unclear. This could alter hinting assumptions and should not be
     guessed without architect input.

## Question

For Phase 0b, should I:

- implement SHA option 2 now and keep P256 namespacing,
- accept SHA option 1 and P256 option 1 and move to Phase A,
- or scope either larger refactor as a separate task before Phase A?
