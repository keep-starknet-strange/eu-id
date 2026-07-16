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

## Q5 — keccak_round GKR offload: COMPLETE (W1+W2+W3a+W3b+W3c) — proof < 1 MB MET

**Status chronology (clarified 2026-07-16):** the first W1/W2 checkpoint stopped before W3,
which is what the historical `STOPPED` sections below describe. W3a/W3b/W3c subsequently landed
in `ae890f0f..73ac7d4e` and met the proof rail; Q8 commit `f4ec6113` later reverted the offload;
Q10 WO-1 has now restored it on the current sound branch. The historical stop was not the final
Q5 outcome.

WO goal (Q4a): offload `keccak_round`'s ~908 log-11 interaction columns into a
LogUp-GKR proof to clear the −83 KB gap to <1 MB. The initial checkpoint delivered the two
foundational, independently-verified prerequisites the §8.2/§S10 STOP called out,
then **stopped before the invasive AIR flip** — the remaining tie-back is a
research-grade build, not a session checkpoint, and an honest stop beats a
forced, soundness-critical integration.

### Landed (green, committed)

**W1 — GKR proof transport in the air-core wire** (`feat/quantum-safe`,
air-core commit).
- air-core carries an opaque per-module post-interaction payload beside the
  `StarkProof`: `prove_with_post_interaction → (StarkProof, Vec<Vec<u8>>)` and
  `verify_with_expected_preprocessed_root_and_payloads(..., &[Vec<u8>])`. The
  existing `prove`/`verify`/`verify_with_expected_preprocessed_root` stay as
  zero-churn wrappers, so the ~40 empty-payload call sites are untouched.
- New `air_core::gkr`: lossless serde transport for stwo's `GkrBatchProof`
  (encode/decode via its public accessors + `GkrMask::new` / `UnivariatePoly::new`
  / `SumcheckProof.round_polys`).
- Trait hooks `AirProver::take_post_interaction_payload` /
  `Air::load_post_interaction_payload` (default no-op).
- FS binding confirmed against the existing doc order: GKR runs inside
  `prove_/verify_post_interaction` (post tree-2), so the proof is bound to
  trees 1/2, the drawn relations, and the claimed sums; tie-back columns commit
  after in tree 3.
- Toy end-to-end test through `prove`/`verify` (GKR grand-product instance):
  round-trips and verifies; **corrupted blob rejects**; **wrong claimed sum
  rejects**. air-core 15/15 green; `cargo check --workspace` clean.

**W2 — MLE-eval component productionized in the fork** (`~/stwo` dev-copy,
local commit `6621507a`).
- Promoted `xor::gkr_lookups::mle_eval` (dead-code example, 1,308 lines) into
  `stwo-constraint-framework::mle_eval` (gated `prover` + `std`), retaining the
  `8c998390` eval-domain fix (quotient evaluated on
  `log_size + composition_log_split`).
- Faithful move of `MleEvalProverComponent` / `MleEvalVerifierComponent`, the
  `MleCoeffColumnOracle` trait, `MleEvalPoint`, the eq / prefix-sum /
  carry-quotient constraint helpers and `build_trace`; local `IsFirst`;
  `mle_eval_at_point` folded in as a `cfg(test)` oracle; `dead_code` allow
  dropped. Example left intact.
- Own 9 unit tests, including both end-to-end prover + verifier components
  through a real commitment scheme. constraint-framework 22/22 green; default
  (non-prover) build clean; the eu-id consumer (`stwo-keccak`) still builds
  against the patched fork.

### Historical checkpoint — STOPPED before W3 (the offload itself)

**No FS/soundness *structural* blocker exists.** Relations are drawn post-tree-1
before GKR runs; the fraction multiset is exactly reproducible from committed
base columns; the claimed sum is preserved. The blocker is engineering magnitude
on a soundness-critical component:

1. **Bespoke denominator oracle (the hard, unbuilt piece).** `keccak_round`'s
   fractions are `N_TOTAL_LOOKUPS` per row across FOUR relation families —
   `keccak_round` link, `xor3`, per-shift `split[1..8]`, `andnot` — batched by
   `finalize_logup_batched(LOGUP_BATCH)` (`keccak_round.rs:763-886`). Each
   denominator is `relation.combine(tuple)` = an affine form `z − Σαⱼ·tupleⱼ` in
   base-column entries. The GKR tie-back needs an `MleCoeffColumnOracle` that
   reconstructs this batched, selector-weighted denominator multiset as an MLE
   over the committed base columns and evaluates it at the GKR OOD point — a
   selector-MLE-weighted linear combination across all four families with
   per-shift split relations. That is a dedicated build (mirroring the
   `toy_horner` de-risk done for `mldsa_coeffs`), not a session checkpoint.
2. **AIR surgery.** `evaluate_round` must drop `finalize_logup_batched` (its
   LogUp is now GKR's); the round's LogUp enforcement is replaced by the W2
   MLE-eval tie-back component committed in the post-interaction tree — an
   invasive change to a soundness-critical `FrameworkEval`.
3. **Claims + shape accounting.** The service's claimed-sums vector and the mdoc
   `hosted_claimed_sums_len` shape gates must move the round's claimed sum from a
   columnar to a GKR-backed slot and fail-closed on the new shape.
4. **Adversarial rails + measurement — downstream of (1)-(3), not yet possible.**
   tamper-round-link-tuple → reject; GKR-claim-swap → reject; a
   `composition_log_split = 2` regression on the tie-back component; existing
   service tamper negatives stay green; then the `pq_perf_probe` +
   `AIR_CORE_SHAPE_DUMP` census with the GKR-blob-net wire-size breakdown.

### Historical checkpoint result vs gates

proof `<1 MB` **NOT met** this session — nothing is removed from the wire yet
(W3 did not land). No campaign scoreboard vs the 72.7 s / 372.7 ms / 34.4 MB
baseline is written, because the offload did not land. The two landed
checkpoints are exactly the transport + productionized-component prerequisites
§8.2 flagged; the residual WO is the round-denominator oracle + AIR flip +
claims/shape accounting + adversarial negatives + measurement, still a dedicated
multi-checkpoint soundness-critical build.

### W3a — oracle de-risk spike LANDED GREEN (obstruction DISSOLVED)

The `MleCoeffColumnOracle` "hard, unbuilt piece" is now **de-risked with a
passing spike**, and the feared arithmetic obstruction (STOP condition
"the batched denominator is not expressible as a low-degree combination of
committed columns at a point") **does not exist**.

**Test:** `keccak_round::gkr_offload_spike::denominator_oracle_reconstructs_at_gkr_ood_point`
(`crates/stwo-keccak/src/keccak_round.rs`, `#[cfg(test)]`). For a real
`keccak_round` witness it (1) rebuilds the exact fraction multiset the
component emits today, in `generate_interaction_trace` order (all four
families: kr-link ±enabler / xor3 / per-shift split / andnot), (2) flattens it
into ONE `Layer::LogUpGeneric` GKR instance and proves it with stwo's
`prove_batch`, (3) reconstructs the numerator AND denominator MLE at the GKR
OOD point purely from base-trace column values via `Relation::combine`, (4)
asserts GKR sum == columnar `claimed_sum`, reconstruction == GKR claims, and a
tampered base cell breaks the reconstruction. Full `stwo-keccak` suite green.

**The dissolving insight — why there is no obstruction.** Lay the flattened
multiset out with the **lookup-slot in the HIGH index bits and the trace row in
the LOW bits**. The OOD point splits `r = (r_slot ‖ r_row)` and the denominator
MLE decomposes canonically:

```
den_mle(r) = Σ_slot eq(slot, r_slot) · den_slot_mle(r_row)
```

Every `Relation::combine` is an **affine** form `z − Σⱼ αⱼ·tupleⱼ` with
**row-independent** coefficients (keys are degree-1 sums of certified limbs,
`lo = rot − hi·4^r`, `u = b1+2·b2` — all fixed-coeff affine maps of base
columns). Multilinear eval is linear and `mle(all-ones) = 1`, so it **commutes**
with the affine combine:

```
den_slot_mle(r_row) == combine([ tupleⱼ_mle(r_row) ]ⱼ)
```

Therefore the oracle only ever needs **each base column's MLE at the single
row-point `r_row`** — the slot-selection collapses into verifier-computable
`eq(slot, r_slot)` weights. The MleEval tie-back stays on the **row-domain**
(`log_size` vars); there is **no `slot × row` domain blow-up** and no
domain-mismatch between the flattened fraction column and the base columns.
Numerators are the same shape: `1` for xor3/andnot/split, `±enabler_mle(r_row)`
for the two kr-links (enabler = base column 0), `0` for slot-padding.

**Sign gotcha (found + fixed):** kr[0] uses `link_fraction(negate=true)`
(−enabler), kr[1] uses `negate=false` (+enabler) — not the intuitive order.

**Concrete W3b recipe (now mechanical, design proven):**
1. **Real oracle** = `MleCoeffColumnOracle` whose `evaluate_at_point(circle_pt,
   mask)` reconstructs the δ-folded (numerator+denominator) coeff-column value
   as `Σ_slot eq(slot,r_slot)·combine(base-col mask entries)` over the row
   circle-domain — i.e. run `evaluate_round`'s tuple-building logic through a
   `PointEvaluator` reading base-column masks, weighted by the `eq(slot,r_slot)`
   constants precomputed from the GKR artifact. One `MleEval` component over
   `log_size` vars ties it to the base-trace commitment (W2). Fold both GKR
   claims into one MleEval via a random δ: check `δ·num_claim + den_claim ==
   verifier_const(r_slot) + mle_c_claim`.
2. **AIR flip:** `evaluate_round` drops `finalize_logup_batched`; its
   `N_INTERACTION_COLUMNS` (≈908 log-11 cols) vanish from tree-2.
3. **Transport:** GKR runs post-tree-1 (relations already drawn), proof travels
   via the W1 `prove_with_post_interaction` payload; verifier feeds it to
   `partially_verify_batch`, gets `(ood_point, claims)`, drives the MleEval
   verifier. `r_row = ood_point[log_slots..]` is the shared MleEval point.
4. **Claims/shape:** move the round's claimed sum from a columnar slot to the
   GKR-backed slot in the service claimed-sums vector; update
   `hosted_claimed_sums_len` + mdoc shape gates fail-closed.
5. **Negatives:** tamper-round-link-tuple → reject; corrupted GKR payload →
   reject (W1 pattern); claim-swap → reject; `composition_log_split = 2`
   regression on the tie-back; existing service negatives stay green.

**Status:** superseded — W3b landed, see below.

### W3b — the flip LANDED (committed, all gates green)

The service's `keccak_round` emits **no interaction columns** (the ~900
batch-4 LogUp columns are gone from tree-2). In their place:

- `stwo-keccak/src/round_gkr.rs`: the fraction multiset (built once by
  `keccak_round::build_fracs`, the same source as the old columnar trace) is
  flattened slot-high/row-low into ONE `Layer::LogUpGeneric` instance and
  proven with `prove_batch` on the shared channel post tree-2. The round's
  claimed sum is computed directly from the fractions (batch-inverse) and
  keeps its old slot in the global LogUp balance.
- Tie-back: a post-GKR channel-drawn δ folds num+den into one coeff column
  `c(row) = Σ_slot eq(slot,r_slot)·(δ·num_slot(row)+den_slot(row))`; a single
  `MleEvalProverComponent`/`MleEvalVerifierComponent` (8 committed tree-3
  columns at round log-size) proves `mle_c(r_row) = δ·num_claim + den_claim −
  pad(r_slot)`. The `RoundCoeffOracle` reconstructs `c` at the OODS point
  purely from the round's committed base-column masks by replaying
  `collect_round_lookups` through a `PointEvaluator` (the W3a affine-commute
  design, verbatim).
- Verifier (fail-closed): payload decode, 1-instance/2-claims/variable-count
  shape gates, `num_out == claimed_sum·den_out` output binding, sumcheck
  replay via `partially_verify_batch`, δ redraw, tie-back component.
- Transport: the W1 payload on both paths; `MlDsaProof` and
  `MdocCircuitProof` carry `post_interaction_payloads` with fail-closed shape
  gates (standalone: exactly `[blob, empty]`; mdoc: exactly one non-empty
  payload iff the service is present).
- Legacy columnar path retained ONLY for the standalone `stark.rs` SHAKE AIR
  (`Eval::gkr_offload = false`); the service always offloads.

**Fork fixes required (dev-copy `~/stwo`, 3 commits):** owned
`MleCoeffColumnOracle` (+ blanket `&T` impl) so the oracle and component live
in one struct; `MAX_N_INTERACTIONS` 4→5 (tree-3-hosted MleEval spans 4
committed trees + its aux tree); **lifted-protocol at-point eval** — the
MleEval components now map the OODS point by
`repeated_double(max_log_degree_bound − log_size)` before all analytic evals
(columns are SAMPLED at that mapped point; identity when max bound == log+1,
which is why same-size unit tests never caught it); **SubDomain evaluation
mode** in the domain quotient — with `log_blowup > composition_log_split` the
committed evals live on the larger blowup domain and the quotient runs on
`committed_domain.split(log_expansion).0` with aux columns evaluated on the
full committed-size domain (blowup-4 production config; blowup-2 tests had
masked this by coincidence of `blowup == split`). Prover-side
oracle-vs-poly assert is env-skippable (`STWO_MLE_EVAL_SKIP_ORACLE_CONSISTENCY`)
so adversarial tests can produce desynced proofs the verifier must reject.

**Adversarial matrix (all green, `stwo-keccak/tests/service.rs`):** corrupted
+ truncated GKR payload → reject; missing payload → reject; blob swapped
between two same-shape proofs → reject (FS replay desync); tampered
round-link tuple → reject (global balance); forged round claimed sum with a
compensating slot → reject (GKR output-claim binding); **tampered committed
base cell → reject (tie-back oracle at OODS — the offload's core soundness
property)**; sum-preserving row-swap inside one slot → reject (eval-at-r_row
binding); positive regression at `log_blowup 4 > composition_log_split 2`
(SubDomain mode, non-trivial expansion). Full gates: stwo-keccak 40/40,
stwo-mldsa 74/74 (+1 ignored), mdoc_mldsa 18/18,
`scripts/check-quantum-only-deps.sh` clean.

### W3c — measured result (release, `RAYON_NUM_THREADS=1`, min-of-3)

Production config FRI `(1,4,26,2)`/pow25, `pq_perf_probe`:

| metric | W3b measured | pre-flip (§8.1) | Δ | target |
|---|---:|---:|---:|---|
| prove  | 5,664 ms | 5,523 ms | +141 ms (+2.6%) | < 1,000 ms (open) |
| verify | 14 ms | 15 ms | −1 ms | MET |
| proof  | **988,402 B** (min 987,074) | 1,082,914 B | **−94,512 B** | **< 1,000,000 B MET** |

Wire breakdown (bytes): queried 689,184 / sampled 164,312 / decommit 59,856 /
FRI 54,516 / **GKR blob 16,872** (inside 20,333 non-STARK metadata) /
commitments 168 / pow 8. The priced ≈ −120 KB net win landed at ≈ −95 KB
(tree-3 commitment + 8 columns + blob + one extra Merkle tree of query
openings eat the difference).

Census (`AIR_CORE_SHAPE_DUMP`): keccak service (m1) interaction tree
1,628 → **728 cols** (5.29 M → 0.33 M interaction cells; −900 cols ==
−1.84 M cells at round log 11), + 8 post-interaction (tree-3) cols
(16 K cells). Proof-wide: 6,200 committed cols / 12.50 M cells (census
trees) vs 7,100 / 14.35 M pre-flip.

**Buy-back FRI frontier** (proof crossed < 1 MB → both points measured):
FRI `(1,3,36,2)`/pow20 (129-bit): prove **3,434 ms** / verify 15 ms / proof
**1,255,082 B**. The frontier is now (5,664 ms, 0.988 MB) @ blowup-4/pow25
vs (3,434 ms, 1.255 MB) @ blowup-3/pow20; blowup-4 stays the shipped config
(proof-size-first rule; < 1 MB gate MET).

### Campaign scoreboard (vs the 2026-07-05 quantum-branch starting point)

| metric | campaign start | Q5/W3b | total |
|---|---:|---:|---:|
| prove (1 thread) | 72.7 s | 5.664 s | **12.8×** |
| verify | 372.7 ms | 14 ms | **26.6×, target MET** |
| proof | 34.4 MB | 0.988 MB | **34.8×, < 1 MB MET** |

Remaining open gate: prove < 1,000 ms (blowup-3 buy-back reaches 3.43 s;
further prove work is a separate campaign — the keccak GKR prove itself adds
only ~0.14 s at the current shape).

## Q6 — prove-time campaign: all three slices priced, all STOP; target unreachable single-thread

Fresh baseline (release, `RAYON_NUM_THREADS=1`, FRI `(1,4,26,2)`/pow25,
`pq_perf_probe`, min-of-3 — thermally loaded machine, cooler runs ~5.2 s):

| metric | measured | target | gap |
|---|---:|---:|---:|
| prove  | 5,417 ms | < 1,000 ms | −4,417 ms |
| verify | 14 ms | < 100 ms | MET |
| proof  | 989,474 B | < 1,000,000 B | MET |

### Q6 phase census (`AIR_CORE_PROVE_TIMING`, one clean run, TOTAL 4.68 s)

| phase | ms | note |
|---|---:|---|
| twiddles + tree0-write | 25 | |
| tree0-commit | 338 | preprocessed LDE+Merkle |
| tree1-write | 320 | witness gen |
| **tree1-commit** | **748** | witness LDE+Merkle |
| tree2-write | 417 | interaction gen |
| **tree2-commit** | **1,040** | interaction LDE+Merkle — biggest single phase |
| build-components | 292 | |
| composition-generation | 597 | quotient eval (Slice A's only surface) |
| composition-commit | 424 | K=2 ⇒ 4 parts LDE+Merkle |
| **prove_values (oods+fri+open)** | **1,748** | FRI + query opening, blowup-4, 26 queries |

Committed shape: 12.5 M cells / ~6,200 M31 cols. Interaction tree 6.28 M cells,
of which coeffs (m2/m3/m6, 100 cols × 2^14 × 3) = 4.92 M = **78 %**. The commit
phases (tree0/1/2 + composition ≈ 2.55 s) and prove_values (1.75 s) together are
~4.3 s of the ~4.7 s total and scale with committed cells × blowup.

### Slice A — per-component composition split: **STRUCTURALLY UNSOUND (measured, reverted)**

Implemented the prover-only per-component excess in the dev-copy
(`constraint-framework/.../prover/component_prover.rs` +
`stwo/.../prover/air/accumulation.rs::finalize` seed). Each component evaluated
its quotient on `2^(trace_log + own_excess)` instead of the uniform
`2^(trace_log + K)` (K=2). **Measured: composition-generation 597 → 340 ms
(−43 %)** — the eval-domain halving works mechanically — but `prove_values`
ballooned to 5.0 s and prove aborted with `ConstraintsNotSatisfied` at the OODS
consistency check.

**Why structural (not a bug):** the accumulator's lift is an isogeny
**pullback** `u_i ∘ π^Δ` (degree-*scaling*), not a degree-preserving embedding.
The verifier (`components.rs::mask_points`/`evaluate_constraint_quotients_at_point`)
lifts *every* component uniformly by its trace-size gap `max_trace − t_i` and
divides by `vanish(max_trace)`; K only reconstructs `f` from `2^K` parts and is
invisible per-component. The composition target is `max_trace + K`, so the lift
amount `target − eval_index` is pinned to `max_trace − t_i`, which forces
`eval_index = t_i + K` **uniformly**. Evaluating at `t_i + excess_i` over-lifts
by `(K − excess_i)` extra doublings ⇒ a higher-degree `f` that mismatches the
verifier (and the ballooned prove_values is FRI on the wrong-degree poly). This
is exactly the "accumulator design makes per-component K unsound" branch.

**Alternative (demote log+2 → log+1 to lower K itself):** K=2 is forced by four
components declaring `log+2` — `stwo-keccak sponge_v`, `predicates range_check`,
`stwo-mldsa sampleinball`, `stwo-sha256 air`. Lowering K to 1 would halve
composition-commit + the composition share of generation/prove_values (~0.4–0.6 s),
but requires restructuring genuine degree-3 constraints to degree-2 across four
independent components — a large multi-component AIR redesign (the mirror of the
+0.8 s that landing uniform-K cost), not a session checkpoint. Priced, deferred.

### Slice B — coeffs union-of-kinds fraction split: **≥5 % needs relation-unification WO; simple merge <5 % (STOP)**

Design pass complete (see `tasks/coeffs-fraction-layout-design.md`). Coeffs emits
24 batch-1 logup fractions/row (21 range-check + eval/WCell/CCell yields), 100
interaction cols. **Batching is walled off**: batch-2 makes the logup constraint
`col·d1·d2 = n1·d2 + n2·d1` degree-3 ⇒ bound `log+2` ⇒ breaks the Horner `[-1,0]`
mask (why `LOGUP_BATCH=1`). So the only sound reduction under the engine's
batch-1/degree-2 model is fewer fraction *streams*.

- **Free sound merge (same relation, disjoint rows):** carry-lo and norm-lo both
  use `rc13` on disjoint rows (carry vs z), so norm-lo `a_lo,b_lo` ride on 2 of
  the 5 carry-lo streams. Saves **2 QM31 cols** ≈ 0.39 M cells ≈ **~1.5 %**.
  Below the 5 % gate — **SKIP**.
- **≥5 % path (relation unification):** replace the 5 independent range relations
  (rc9/rc13/rc8/rc7/ternary) with ONE arity-2 `(value, bound_id)` relation +
  combined preprocessed table. Then disjoint-kind streams share columns; max
  concurrent range uses/row = 10 (z-digit: 6 rc9 + 4 norm; carry: 5+5), so 21
  range streams → **10**. Total logup 24 → 13 cols. Saves **11 QM31 = 44 M31 ×
  2^14 × 3 = 2.16 M cells** (interaction 6.28 M → 4.12 M, −34 %), price
  **≈ −0.5 to −0.8 s** (hits tree2-write/commit + prove_values + composition-gen).
  Matches the task's −2…−3 M / −0.6…−1.0 s estimate. **Soundness-critical**
  (a value must never be checkable against the wrong `bound_id` — needs the
  air-writer skill + a per-former-table "in-other-bound" negative each) ⇒ a
  dedicated multi-checkpoint WO, not a session burst (cf. Q4a/Q5 GKR precedent).

### Slice C — FRI frontier: **already rejected in Q5**

blowup-3/pow20 reaches prove 3.43 s but proof **1.255 MB** — busts the
never-regress-above-1 MB rail. No re-open.

### Q6 residual arithmetic — why < 1,000 ms is unreachable single-thread

The workload floor is fundamental: 12.5 M committed cells (keccak service 3.45 M
+ 3× ML-DSA 2.46 M each + glue) LDE'd and Merkle-committed at blowup-4, then
FRI-opened. Commits + prove_values ≈ 4.3 s of the ~4.7 s and shrink only with
(a) fewer cells or (b) lower blowup (rejected). The single sound cell lever
(Slice B unification, −2.16 M cells ≈ −0.6 s) would leave prove ≈ 4.5 s. Slice A
is unsound; K-demotion (~−0.5 s) is a 4-component redesign. Reaching < 1,000 ms
from 5.2 s is a ~5× cut = removing ~80 % of the committed cells, i.e. the ML-DSA
coeffs + keccak service themselves — not achievable by column-shaving.
(Note: the pinned gate is `RAYON_NUM_THREADS=1`; with desktop threads this path
runs ~8× faster and would clear 1 s, but the 1-thread gate stands.)

### Q6 outcome

No slice landed a sound measured improvement; the three numbers are unchanged
from the baseline above (dev-copy + eu-id trees reverted to clean —
`stwo@4f877db2`, `eu-id@73ac7d4e`, no net code change). Standing scoreboard vs
campaign start (72.7 s / 372.7 ms / 34.4 MB) is unchanged from Q5: **12.8× /
26.6× (MET) / 34.8× (MET)**; prove < 1 s remains open and is out of reach for
single-thread column work — future levers are the two priced WOs (Slice B
relation-unification −0.6 s; K-demotion −0.5 s) or multi-threading the gate.
