# Quantum-safe-only branch and SHA campaign

## 1. Objective

Turn `feat/quantum-safe` into the single ML-DSA product branch, remove classical P-256 and
ec-coprocessor product paths from its build and wire surfaces, then replace the inherited SHA-256
machinery that is disproportionate to the remaining hidden-attribute workload.

The classical implementation remains on its existing branches. The quantum branch may intentionally
break proof-wire compatibility with mixed/classical builds; malformed or stale proof shapes must
still fail closed.

## 2. Measured starting point

S9, `ce26b934`, release, `RAYON_NUM_THREADS=1`:

| metric | baseline | target |
|---|---:|---:|
| prove | 8,232 ms | < 1,000 ms |
| verify | 14 ms | < 100 ms |
| proof | 1,109,272 B | < 1,000,000 B |
| committed columns | 7,290 | fewer is better |

Proof bytes are column-bound: queried 810,360 B, sampled 190,720 B, FRI 53,316 B, decommit
51,240 B, other 3,636 B. The measured marginal price is about 145 B per committed M31 column.

## 3. Product split contract

The quantum branch has one supported signature scheme: ML-DSA-65 for issuer, device, and optional
revocation authority. Its default workspace build, SDK, FFI, examples, and tests must not depend on
`p256`, `ecdsa`, `stwo-p256`, or `eu-id-ec-coprocessor`.

Shared cryptographic crates `air-core`, `stwo-keccak`, and `stwo-mldsa` remain textually shared where
possible so backend/security fixes can still be cherry-picked. `stwo-sha256` remains temporarily
shared through Q2; Q3 may introduce a quantum-specific consumer only after its design and soundness
rails are written.

The local workspace Stwo patch at revision `8c998390` is required for dynamic composition splitting
and batch-4 LogUp. Branch cleanup must not remove or silently replace it.

## 4. Q1 — branch divergence

1. Remove classical crates from workspace membership and classical optional dependencies/features
   from `eu-id-prover`, `sdk`, and `eu-id-ffi`.
2. Make the quantum configuration unconditional/default and convert the probe/gates to exercise that
   build without feature aliases.
3. Delete classical-only source modules, APIs, proof fields, statement variants, and verifier arms.
   Simplify cfg branches only after the compiler proves the branch is unreachable.
4. Preserve ML-DSA fixture generation and native oracle tests as development-only dependencies.

Acceptance:

- `cargo check --workspace`
- `scripts/check-quantum-only-deps.sh`
- release `mdoc_mldsa`, `credential_pipeline`, and SDK tests
- `stwo-keccak`, `stwo-mldsa`, and `stwo-sha256` tests unchanged/green
- default dependency tree contains none of the four banned classical crates

## 5. Q2 — direct revocation message provider

The revocation message is exactly
`LE64(id_lo) || LE64(id_hi) || LE32(epoch)`. Today the merged SHA module hashes it only to reuse
SHA field exposure; the digest is discarded. The exposure duplicates the same 20 bytes under the
range-bind field id and `HOSTED_MSG_FIELD_ID`.

`MdocRevocationRangeBind` already owns and constrains the canonical `id_lo`/`id_hi` witness, binds
the public epoch, and participates in the same global LogUp. Q2 makes it the sole producer of the
20 tuples consumed by the hosted ML-DSA message bridge. No separate byte-provider component is
needed.

Soundness obligations:

- produce `HOSTED_MSG_FIELD_ID` tuples with negative multiplicity from the range component;
- retain in-AIR `[0,256)` pinning for every private bound byte after SHA range lookups disappear;
- keep the epoch bytes constant-pinned to the public epoch;
- remove the revocation slot from both prover- and verifier-derived merged SHA schedules;
- keep proof serialization free of the private revocation bounds;
- reject message/signature mismatch, tuple tampering, slot replay, and stale wire shapes.

The remaining SHA slots are hidden `IssuerSignedItem` attributes. Their SHA-256 digests are required
by ISO mdoc `ValueDigests`; they cannot be host-computed because the preimages are private.

## 6. Q3 — attribute-only SHA design gate

Q3 begins with a fresh post-Q2 load census. The inherited `stwo-sha256` table set has roughly 9.3M
fixed cells at log 17 and was designed to amortize thousands of blocks. The quantum path has only a
few hidden attributes, so a replacement must optimize small load rather than preserve P-256-era
throughput.

No implementation begins until the design records:

- supported message length/block bounds and padding;
- trace layout and exact column/cell model;
- SHA-256 round recurrence and range/bitwise constraint strategy;
- degree bounds and composition blowup compatibility;
- public digest and private field-exposure relation contracts;
- transcript/wire shape and verifier-reconstructible values;
- differential and adversarial test matrix;
- estimated proof/prove/verify result versus the S9/Q2 census.

## 7. Verification and measurement discipline

The metric of record is a release build with `RAYON_NUM_THREADS=1`. Run same-session A/B where a
checkout comparison is possible; report min and median when thermal drift is visible. Use
`AIR_CORE_SHAPE_DUMP=1` for module columns/cells and `AIR_CORE_PROVE_TIMING=1` for phase timings.

Every pushed checkpoint contains only one coherent milestone, its tests, and its task/design record.
