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

## 8. Q4 — proof/prove frontier: both slices priced, both STOP

### 8.1 Measured baseline (this session)

Release, `RAYON_NUM_THREADS=1`, FRI `(1,4,26,2)`/pow25, probe
`crates/eu-id-prover/examples/pq_perf_probe.rs`:

| metric | measured | target | gap |
|---|---:|---:|---:|
| prove  | 5,523 ms | < 1,000 ms | −4,523 ms |
| verify | 15 ms | < 100 ms | MET |
| proof  | 1,082,914 B | < 1,000,000 B | −82,914 B |

`AIR_CORE_SHAPE_DUMP` module map: m0 SHA-glue; **m1 keccak service** (318 pre /
2,068 trace / 1,628 interaction = 4,014 cols, 5.29 M cells); m2/m3/m6 ML-DSA
instances (coeffs-dominated, ~2.5 M cells each); m4 merged SHA (951 cols).
Marginal proof price ≈ 145 B / committed M31 column (queried_values dominate).

### 8.2 Q4a — GKR offload of the keccak-service LogUp — **STOP (documented)**

**Interior census (base interaction cols in m1, the offload candidates):**

| component | fractions | interaction base cols | log | relations |
|---|---:|---:|---:|---|
| sponge_v     | `5·RATE+4 = 684` (÷batch 4 = 171) | **684** | 6  | produces cross-module `HashIo` |
| keccak (perm)| 4 (÷2)                            | 8       | 11 | internal `KeccakState` |
| keccak_round | `N_TOTAL_LOOKUPS ≈ 907` (÷4 = 227) | **908** | 11 | internal `KeccakState`/xor3/andnot/split |
| tables ×9    | 9×4                               | 36      | 8/16 | table channels |

**Column arithmetic (passes the >80 KB gate):** the tie-back is cheap in
columns — `MleEvalProverComponent` commits ~2 secure helper cols (eq +
prefix-sum accumulator) per evaluated MLE per domain (~16–30 base cols for a
numerator+denominator pair at one log). Offloading `keccak_round` alone:
`(908 − ~30) × 145 B ≈ +127 KB`, minus a few-KB `GkrBatchProof` blob → net
**≈ +120 KB**, well over 80 KB and enough to clear the −83 KB proof gap by
itself. (sponge_v adds another ~+99 KB but its `HashIo` production is the
cross-module relation ⇒ larger soundness surface; prefer round-only.)

**Why STOP — the integration cost is structural, not the column cost:**

1. **No GKR transport in the proof wire.** `air_core::prove` returns
   `StarkProof` only; `Air::verify_post_interaction(channel)` has no path to
   *receive* a `GkrBatchProof`. Requires changing air-core's prove/verify
   surface (or a module-emitted-blob mechanism), adding a field to
   `MdocCircuitProof` (`crates/eu-id-prover/src/mdoc.rs:2200`), bincode
   serialization, and threading through `prove/verify_mdoc_circuit`. The
   air-core post-interaction hooks (`prove_post_interaction` /
   `write_post_interaction` / `post_interaction_log_sizes` /
   `verify_post_interaction`) exist but are empty stubs — they commit tie-back
   *columns* (tree 3) and mix the transcript; they carry **no** GKR proof data.
2. **The MLE-eval component is a fork example, not API.**
   `/Users/lucas/stwo/crates/examples/src/xor/gkr_lookups/mle_eval.rs`
   (`#![allow(dead_code)]`, `TODO(andrew): Remove in downstream PR`, 1,308
   lines). Productionizing needs a bespoke `MleCoeffColumnOracle` computing the
   `keccak_round` denominator (relation-combination of committed base columns)
   at the GKR OOD point, wired through the post-interaction hooks. (Fork commit
   `8c998390` fixed `MleEvalProverComponent` eval-domain under
   `composition_log_split > 1` — the framework path is de-risked, the
   productionization is not.)
3. **Soundness rework.** The GKR output claim must bind the SAME drawn
   `KeccakRelations` randomness (drawn pre-tree-1) and equal `round_claimed_sum`
   so the global LogUp balance (service claimed sums + consumer claimed sums = 0)
   is preserved with the round side proven by GKR instead of columns. Targeting
   `keccak_round` keeps this internal (its relations are service-internal;
   `HashIo` stays columnar), but the OOD/relation binding + adversarial rails
   (tamper sponge byte → GKR imbalance; claim-swap negatives) are the real risk.

**Verdict:** column-arithmetically worth it (net ≈ +120 KB, the one lever that
reaches <1 MB), but a dedicated multi-checkpoint soundness-critical build — not
a session checkpoint. **Recommended future WO scope:** `keccak_round`-only GKR
offload (131 KB gross, service-internal soundness surface, clears <1 MB alone);
land the wire-transport + productionized `MleEvalProverComponent` first behind
adversarial negatives, then flip round to GKR.

### 8.3 Q4b — coeffs 2-per-row repack — **STOP (net-neutral, twice-confirmed)**

Coeffs component (`crates/stwo-mldsa/src/coeffs/`) per instance @ log 14:
17 preprocessed + 15 base + 100 interaction = 132 cols; active 9,204 of 16,384
rows (43.8 % padding); ≈ 2.16 M cells (of which interaction = 4 acc-coord +
96 logup = 1.64 M, the dominant term). `N_LOGUP_ENTRIES = 24` fraction streams,
`LOGUP_BATCH = 1`.

**Committed cells = columns × 2^log_size.** Two lookup uses in the SAME row need
DISTINCT fraction columns (a column carries one value per row), so packing 2
coefficients per row doubles the kind-specific fraction streams (24 → ~48; only
the group-end eval-yield stays ~1) and doubles the per-coeff base/preproc
columns, while halving rows (log 14 → 13):

- interaction: 192 base cols × 8,192 = 1.57 M = **identical** to 96 × 16,384;
- net: cells **invariant** (a pure reshape); columns **increase** 132 → ~252.

Effect on targets: **prove** ~ Σ cells ⇒ ~flat (a small `n·log n` edge from
log 14→13 is offset by more columns' fixed commit overhead — nowhere near the
projected −1…−1.5 s); **proof** gets **worse** (+~120 cols × 3 × 145 B ≈ +50 KB),
moving *away* from <1 MB.

This matches the codebase's own S9 record verbatim
(`tasks/keccak-service-design.md` line 566): *"coeffs 2/row repack is forbidden
AND net-neutral for a column-bound proof (doubles per-row cols, halves rows)."*

The real coeffs waste is the **union-of-kinds gated fraction layout** (every row
carries fraction slots for all six kinds even though a row is one kind), which
needs per-kind component splitting or engine column-packing (design doc §S9
flags the latter as out of scope) — NOT row-packing. The `+1` composition-bound
Horner-mask hard constraint also forbids the naive 2-slot accumulator.

**Verdict:** STOP — no measured win, worsens the proof-size target.

### 8.4 Q4 outcome

No slice landed a measured improvement; the three numbers are unchanged from the
baseline above (single FRI frontier — no code change). The only lever that
reaches <1 MB is the Q4a `keccak_round` GKR offload, scoped as a dedicated WO.
