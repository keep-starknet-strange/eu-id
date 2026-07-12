# Perf campaign — full mdoc + revocation (sha256+p256) — 2026-07-12

Goal: prove <1s, verify <100ms, proof <700KB (full TS13 N=1 tuple).
Baseline @ 730e9294 (1-thread, M4 Max, ts13_full_probe BENCH_ITERS=5):
prove 2,853ms / verify 255ms / proof 4,517,637B.
Rule: every WO lands with a measured ts13_full_probe number. No number, not done.

## Status ledger

| merge | WO | prove | verify | proof B |
|---|---|---|---|---|
| 730e9294 | baseline | 2,853 | 255 | 4,517,637 |
| 4244afb9 | WO-A engine+batch4 | 3,189 | ~248 | 3,608,069 |
| 589d1d05 | WO-C1b c6 deletion | 3,177 | 240 | 3,528,653 (STARK 2,454,341 / coproc 1,073,431) |
| 1157d10e | WO-C2 FFT claim-batch verify | 3,148 | 190 | 3,528,173 |
| 1157d10e | 2026-07-13 takeover re-probe | 3,393 | 198 | 3,527,981 |
| worktree | WO-C3 delete redundant C13 | 3,315 | 166 | 3,241,093 |
| worktree | Ligero full-domain sampler fix | 3,252 | 163 | 3,243,317 |
| experiment | Ligero ℓ=512 (N=5) | 3,290 | 258 | 3,037,125 |
| experiment | Ligero ℓ=1024 (N=1) | 4,108 | 654 | 3,002,885 |
| worktree | STARK fold step 2→3 (N=5) | 3,088 | 162 | 3,228,709 |

## Work orders

- [x] WO-A — engine unlock + logup batch-4. MERGED 4244afb9. Proof −909KB
      (queried −820KB, sampled −88KB); prove +336ms = uniform-K lifting tax
      (composition_log_split 1→2), accepted — WO-B rides the same K=2.
- [x] WO-C1 — E1c c6 repack — CLOSED INFEASIBLE (GKR: no advice wires;
      best sound digit repack misses gate). Superseded by WO-C1b.
- [x] WO-C1b — c6 family DELETED after redundancy proof. MERGED 589d1d05.
      committed_values 31,121→27,920. See redundancy argument below.
- [x] WO-B — split-mask virtual columns CLOSED UNSAFE AS DESIGNED. The verifier
      opens both shares at OODS: `p0(z) = mult(z) - R(z)` and `p1(z) = R(z)`,
      so it recovers the supposedly hidden value as `p0(z) + p1(z) = mult(z)`.
      No implementation exists in the engine worktree. Preserve the current
      Class-D dummy-row blinding unless a hiding commitment/protocol redesign is
      separately reviewed.
- [x] WO-C2 — claim-batch verify algorithmics. MERGED 1157d10e. Replaced the
      per-opening dot products with one full-codeword circle FFT per row without
      changing proof bytes or protocol semantics; current takeover re-probe is
      198ms verify versus the campaign's original 255ms baseline.
- [ ] WO-C4 — portable P-256 field backend. ISOLATED RED EXPERIMENT in
      `.claude/worktrees/agent-a0185ac70915e9f79`: the edge differential test
      currently fails on squaring, so none of its code is merged or accepted.
- [x] WO-C3 — delete redundant c13 slope-inverse family. IMPLEMENTED AND
      VERIFIED. Committed values 27,920→15,479; opened rows 112→63; proof
      −286,888B; verify −32ms against the takeover re-probe. See equivalence
      proof below.
- [x] P-256 ladder regression — executable proof now documents that replacing
      both accumulator transcripts with repeated valid on-curve generator
      points passes every implemented family and the proof verifier even though
      the native witness checker rejects it.
- [ ] P-256 relation repair — BLOCKED on a reviewed combined spec. There is no
      transition gadget to reuse, and constraining transitions alone is
      insufficient: C3's field equations also need a sound integer/limb proof
      of the scalar reductions modulo n. Do not claim the current coprocessor is
      a sound ECDSA verifier until both obligations land.
- [x] Ligero Task 4 — restore Circle proximity sampling over the full codeword.
      The inherited RS-prefix exclusion invalidated the v4 full-domain error
      calculation; fixed before any larger-row profile sweep.
- [x] WO-D — PCS retune on shrunk circuit: sweep blowup 2/3 × queries/pow,
      Ligero ℓ A/B. Ligero ℓ=512/1024 CLOSED NO-GO for production after
      measurement. STARK fold step 3 is the measured production Pareto point:
      prove −164ms, verify −1ms, proof −14,608B versus the full-domain-sampler
      N=5 baseline.
- [ ] Final: suites + negatives green, pins repinned, docs + memory updated,
      single- and multi-thread numbers reported.

## WO-B split-mask virtual columns (a.k.a. WO-D2R Option A)

> **REJECTED 2026-07-13:** this section is retained as historical design
> context only. It incorrectly claims that `(mult - R, R)` is jointly
> independent of `mult`; the pair deterministically reveals `mult` by addition
> at every common sampled point. The physical PCS openings expose both shares,
> including at OODS, so the construction does not preserve Class-D zero
> knowledge. Do not implement it without a hiding commitment or a protocol that
> never reveals both share evaluations.

Goal: delete the Class-D blind-doubling of the shared SHA-256 tables (`2^17 → 2^16`)
and replace it with split-mask virtual columns, so every secret column commits at
`2^16` plus a tiny `~2^12` mask column instead of a doubled `2^17` column.

### Construction

Today `crates/stwo-sha256/src/shared_tables.rs` (`blind_extend` :179, `emit_blind`
via `producer_blind_frac_column`, `is_dummy` selector, `blind_log_size` = `LOG_SIZE_16 + 1`)
doubles every real `2^16` producer multiplicity column and its LogUp accumulator to
`2^17` by appending fresh random cells over an unreachable dummy-key upper half, with a
`(1 − is_dummy)` gate zeroing the dummy numerators so they never touch the LogUp balance.
That doubling is the ~4.4 M committed cells WO-B removes.

Replacement, per secret column (the 12 producer multiplicity trace columns plus the
7 paired LogUp-accumulator `SecureField` columns = 28 base columns of the shared tables):

- commit `p0 = mult − R` as a normal `2^16` column,
- commit `p1 = R` as a tiny column of `log_size = LOG_TINY` (see `t` below), where `R`
  is a fresh per-proof random low-degree polynomial (`thread_rng`, matching the existing
  `blind_extend` CSPRNG, never transcript-derived),
- the constraint system reads the **virtual** column
  `f = p0 + (v_n + 1)·p1 = mult + v_n·R`, where `v_n = coset_vanishing` of the
  component's canonic `2^16` coset (`stwo/src/core/constraints.rs:12`).

On the trace coset `v_n = 0`, so `f == mult`: every constraint, the LogUp balance, and
every claimed sum are **bit-identical** to the unmasked circuit. Off-domain the opened
LDE cells reveal only `mult(x) − R(x)` (from `p0`) and `R(y)` (from `p1`), which are
uniform by a full-rank evaluation-matrix argument given the `t` margin below.

### `t` sizing (dim R), from the ACTUAL production PcsConfig

`mdoc_production_pcs_config()` (`crates/eu-id-prover/src/mdoc.rs:5646`):
`FriConfig::new(log_last_layer_degree_bound=1, log_blowup=2, n_queries=54, fold_step=3)`.

```
n_queries      = 54
2^fold_step    = 2^3 = 8
n_samples      = 2   (max OODS mask points on a masked column: the accumulator's [-1, 0];
                      multiplicity columns use [0] → 1)

t ≥ 2 × (n_queries × 2^fold_step + n_queries + n_samples)
  = 2 × (54 × 8       + 54        + 2)
  = 2 × (432 + 54 + 2)
  = 2 × 488
  = 976
```

`dim(R) = 2^LOG_TINY ≥ t = 976 ⇒ LOG_TINY ≥ 10`. Pick **`LOG_TINY = 12`** (4096),
giving ~4.2× headroom over `t` and matching the feasibility study's "~11–12". Tiny/full
ratio `4096 / 65536 = 6.25 %`, versus the current `+100 %` doubling.

### Soundness note — PENDING LUCAS CRYPTO REVIEW

(i) **Committed columns within native FRI spaces.** `p0` is a genuine degree-`<2^16`
circle column and `p1` a genuine degree-`<2^12` circle column; both are committed and
FRI-folded in their own native spaces (the lifted-Merkle mixed-height commit path,
`poseidon252_lifted.rs` / `pcs/utils.rs:207 prepare_query_positions_for_height`, already
exercised by the mixed tiny/large parity test @ `116b03c0`). Nothing is committed outside
a native low-degree space, so FRI soundness is unchanged. A `p1` that carries degree above
`2^LOG_TINY` is rejected structurally by the lift bound (the tiny tree only has `2^LOG_TINY`
leaves; a higher-degree poly cannot be consistently opened) — this is the engine negative
(b) below.

(ii) **OODS identity over the virtual `f`, degree budget ≤ log+2.** The verifier and
prover both evaluate `f(z) = p0(z) + (v_N(z)+1)·p1(z)` at the OODS point (and at shifted
mask points `z·g^{−k}` for offset `−k`, with `v_N` shifted identically). Because
`f = mult + v_n·R` as a formal polynomial and `deg(v_n·R) = 2^16 + 2^12 < 2^{17}`, the
worst-case constraint monomial in `f` rises by at most one binary order, so the affected
components need `max_constraint_log_degree_bound = log_size + 2`. `composition_log_split`
is already `2` on this circuit (WO-A), so the composition domain already accommodates
degree `log+2` for free — but each split-mask component MUST assert
`max_constraint_log_degree_bound == log_size + 2` (not `+1`), else the composition-domain
doubling desyncs the shifted interaction mask and OODS fails `ConstraintsNotSatisfied`
(see MEMORY: "M4 CRITICAL framework constraint"). A cheating prover cannot gain: on the
trace coset `f == mult` regardless of `R`, so no `R` can satisfy a constraint that `mult`
violates; off-coset `R` only affects openings, never the constraint identity.

(iii) **ZK simulatability with the `t` sizing.** The simulator samples `R` uniform of
dim `t`. The verifier observes `p0` and `p1` only at the `n_queries` FRI query positions
(× `2^fold_step` fold siblings) and the `n_samples` OODS points — at most
`n_queries·2^fold_step + n_queries + n_samples = 488` linear functionals of `R` per column.
With `t = 976 ≥ 2 × 488` and `R` uniform, the evaluation matrix of these functionals is
full-rank w.h.p., so `mult − R` and `R` are jointly uniform and independent of `mult` at
every opened location. The doubled-dummy scheme's ZK is thereby preserved.

### Engine work (in `/Users/lucas/stwo-split-mask`, `feat/split-mask-columns`)

New `EvalAtRow` primitive (transparent virtual-column read):

```rust
/// Reads a split-masked base column committed as two physical trace columns:
/// p0 at the component's full size and p1 at `tiny_log_size`. Returns the virtual
/// value f = p0 + (v_n + 1)·p1 (== the unmasked value on the trace coset).
fn next_masked_trace_mask(&mut self, tiny_log_size: u32) -> Self::F;
/// Extension-field (SecureField) variant for the LogUp accumulator columns,
/// consuming SECURE_EXTENSION_DEGREE p0 base columns then the same count of p1.
fn next_masked_extension_mask<const N: usize>(&mut self, tiny_log_size: u32,
    interaction: usize, offsets: [isize; N]) -> [Self::EF; N];
```

Per-evaluator implementation (fold injected where `v_n` is available to each):

1. **`InfoEvaluator` (`info.rs`)** — record, per masked column, its `tiny_log_size` in a
   new `TreeVec<Vec<u32>>` `column_log_sizes` (default = component `log_size`, override =
   `tiny_log_size`). Drives the two `FrameworkComponent` size hooks below.
2. **`FrameworkComponent` (`component.rs`)** — `trace_log_degree_bounds` (:211) returns the
   per-column sizes recorded by Info instead of `vec![log_size; n]`; `mask_points` (:227)
   uses each column's own coset step (offset-0 masks are size-independent; the
   accumulator's `−1` uses the full-size step, applied to `p0`; `p1`'s `−1` uses the tiny
   step); `evaluate_constraint_quotients_at_point` (:245) computes and passes
   `v_N(z) = coset_vanishing(CanonicCoset::new(log_size).coset, z)` (component's own coset,
   NOT `max_log_degree_bound`'s) to `PointEvaluator`.
3. **`PointEvaluator` (`point.rs`)** — new field `v_n_at_point: SecureField` (+ shifted
   values for used offsets); fold `p0(z·g^{−k}) + (v_N(z·g^{−k})+1)·p1(z·g^{−k})`.
4. **`get_constraint_quotient_inputs` / domain evaluators
   (`prover/component_prover.rs:82`, `simd_domain.rs`, `cpu_domain.rs`)** — precompute a
   `(v_n + 1)` vector over the eval domain. `v_n` on the eval domain is exactly
   `denom_inv.inverse()` elementwise (`denom_inv[i] = coset_vanishing(trace_domain.coset(),
   eval_domain.at(i)).inverse()`, `component_prover.rs:108`), so `(v_n+1)` reuses the
   existing per-`log_expand`-block structure. `p1`'s columns are extended to the eval
   domain from their tiny `2^12` poly via `get_evaluation_on_domain` (already generic over
   poly size). Fold multiplies `p1`'s extended row (indexed at the same shifted position as
   its offset) by `(v_n+1)` before adding to `p0`.
5. **`AssertEvaluator` / `relation_tracker`** — on the trace coset `v_n = 0`, fold is
   `p0 + p1`; trivial.
6. **Degree budget** — each split-mask `FrameworkEval::max_constraint_log_degree_bound`
   returns `log_size + 2`; assert `composition_log_split >= ` the excess in the AIR builder.

Engine negatives (in the stwo worktree):
(a) tamper `p1` (or `p0`) at a query position ⇒ OODS `ConstraintsNotSatisfied`;
(b) a `p1` declared `tiny_log_size` but carrying degree `> 2^tiny_log_size` ⇒ rejected by
    the lift bound (tiny tree cannot open a higher-degree poly consistently).
Model the whole primitive on the composition-split mid-basis fold
`extract_composition_oods_eval` (`stwo/src/core/proof.rs:35`, commit `96a8c667`).

De-risk milestone (toy_horner precedent): a minimal `FrameworkComponent` at `log_size 4`
with one masked column (`p0` `2^4` + `p1` `2^2`) that proves + verifies + rejects (a)/(b),
BEFORE touching the 16 k-line `stwo-sha256` shared-tables module.

### EU-ID work (this worktree)

1. `shared_tables.rs`: delete `blind_extend` / `emit_blind` / `is_dummy` / `DUMMY_KEY_BASE`
   / `blind_log_size` sites (:179, :278, :479, :493, `producer_preprocessed_cols` +1,
   `round/sigma/range_blind_rows`); producers + accumulators return to `2^16` with `(p0,p1)`
   pairs for every secret column. Preprocessed table CONTENT is public → preprocessed drops
   the `is_dummy` column and returns to `2^16`.
2. Witness: sample `R` per proof (`thread_rng`), build `p0 = mult − R` / `p1 = R` columns.
3. Update consumers of `blind_log_size` / dummy selectors across `multiplicities.rs`,
   `trace.rs`, `interaction.rs`, `air.rs`, `field_exposure.rs`, and eu-id-prover glue.
4. Repin preprocessed roots (layout changed): find pinned root constants /
   `PreprocessedRootMismatch` sites in eu-id-prover, repin per `git log --grep=repin`.
5. Port Class-D negatives: `class_d_sha_tables_dummy_region_is_doubled_and_randomised`
   (`shared_tables_composition.rs:231`) → split-mask equivalent (p0/p1 present, R fresh
   per proof, `f == mult` on trace coset); `class_d_sha_table_balance_tamper_rejected`
   (:302) → tampered p0/p1 rejected.

### Status / gates

Closed before implementation. `/Users/lucas/stwo-split-mask` remains clean at
`8c998390`; the only eu-id prep commit redirects local Cargo patch paths and is
not merged. The privacy failure above is protocol-level, so evaluator tests or
tamper negatives cannot make this construction acceptable.

## 2026-07-13 takeover audit

- Fresh command: `RAYON_NUM_THREADS=1 BENCH_ITERS=5 cargo run --release -p
  eu-id-prover --example ts13_full_probe`.
- Fresh result at `1157d10e`: prove median 3,393ms (runs 3,592 / 3,260 / 3,393 /
  3,485 / 3,315), verify median 198ms, proof 3,527,981B.
- Proof bytes: STARK 2,453,669B, coprocessor 1,073,431B, metadata 881B.
  STARK queried values remain the dominant 2,031,952B; coprocessor proximity
  openings are 704,712B + 265,416B.
- Reproducibility blocker: the declared Stwo dependency is pinned to git rev
  `8c998390`, but the workspace `[patch]` resolves it from absolute local paths
  under `/Users/lucas/stwo`. Publish/verify that engine revision and remove the
  absolute patch before treating a remote CI result as reproducible.


## WO-C3 C13 redundancy argument and result

**Change:** removed the C13 slope-inverse circuit family, its 1,026 interior
ladder inverse witness slots, and the final C11↔C13 consistency pair. The final
add inverse remains in the native witness and is enforced directly by C11.

**Why the accepted verifier relation is unchanged:** C13 committed 1,027
independent pairs and checked `d_i * v_i - c² = 0`. Only the final pair was
opened and cross-bound to C11; the other 1,026 pairs were never bound to C12's
separately committed accumulator points. For any reduced witness satisfying
C11, extend it to the old relation with `c = 1`, every interior pair `(1, 1)`,
and the final pair `(b_x-a_x, denom_inv)`. C11 already enforces
`(b_x-a_x) * denom_inv = 1`, so every old C13 equation and cross-check passes.
Projection from an old satisfying witness to the reduced families is immediate.
Thus the existential statement relation is equal in both directions; proof
bytes and transcript layouts intentionally change.

This dedup does **not** close the pre-existing critical ladder gap: C12 proves
the accumulator points are on-curve, but no implemented family constrains their
double/add transitions or binds the sequence to C3's u1/u2. The design document
now states that boundary explicitly instead of claiming C13 supplied linkage.

The gap now has an executable regression:
`forged_ladder_accumulators_must_reject` replaces all C12 accumulator points
with the valid P-256 generator. `verify_witness` rejects the transcript, but the
six implemented circuit families, an unchecked proof, and the public verifier
accept it. The test is ignored and asserts current-broken acceptance; it must be
flipped to rejection when the combined scalar-reduction and ladder-transition
spec is implemented. This demonstrates the missing relation without pretending
an honest-signature input is itself a forged public signature.

Measured at the 2026-07-13 takeover tree, single-thread, five iterations:

| metric | before | after | delta |
|---|---:|---:|---:|
| prove median | 3,393ms | 3,315ms | −78ms |
| verify median | 198ms | 166ms | −32ms |
| proof bytes | 3,527,981 | 3,241,093 | −286,888 |
| coprocessor bytes | 1,073,431 | 784,863 | −288,568 |
| committed values | 27,920 | 15,479 | −12,441 |
| encoded/opened rows | 112 | 63 | −49 |
| ECDSA families per signature | 7 | 6 | −1 |

Verification: release non-ignored coprocessor suite passed with the known G4
inventory-file test skipped; all 23 ignored proof/forgery tests passed; focused
C11 bad-inverse and zero-denominator negatives passed; bundle missing/extra
entry checks fail closed; exact gate count is 3,239 quadratic terms. The full
`ts13_evidence_pack_n1_measurements` proof passed (3,296ms prove / 169ms verify /
3,146,277B in that fixture), and the fully-qualified
`mdoc::coprocessor_tests::revocation_carried_instance_tampering_fails_closed`
negative passed. Clippy is clean for changed targets after allowing the crate's
documented pre-existing lint classes; unsuppressed `-D warnings` remains red on
those pre-existing issues.

## Ligero full-domain sampler correction

The production Circle code is non-systematic, but `ligero_proximity_indices`
still excluded indices `[0, row_len)` as if they were the RS systematic prefix.
The v4 soundness formula uses the full 4,096-column domain. Conditioning queries
onto only 3,840 columns lets an adversarial error pattern spend up to 256 errors
in the never-sampled region and degrades the conservative proximity term to
roughly 116 bits instead of the documented 132.16 bits.

The sampler now applies the prefix exclusion only to `LigeroCode::Rs`; Circle
draws distinct indices over its full codeword. A deterministic regression pins
both halves of that rule, the soundness gate now includes production v4, and the
honest bundle test requires at least one opening in the formerly excluded Circle
range. All non-ignored tests and all 23 ignored proof/forgery tests pass.

Five-run TS13 measurement after the correction: 3,252ms prove / 163ms verify /
3,243,317B. Bundle size and row shape are unchanged; the ~2KB STARK variation is
Merkle/query randomness. This is a soundness restoration with no measurable
performance cost.

## Ligero aspect-ratio re-sweep (post-C13)

After fixing the sampler, temporary compile-time ℓ=512 and ℓ=1024 profiles
were implemented with full geometry round-trip tests and exact ≥132-bit
soundness pins. Both use 176 openings; ℓ=512 is `(k,n,e) =
(1024,8192,3326)` and ℓ=1024 is `(2048,16384,6654)`.

Measured results:

| profile | samples | prove | verify | proof B | coprocessor B |
|---|---:|---:|---:|---:|---:|
| production ℓ=256 | 5 | 3,252ms | 163ms | 3,243,317 | 784,863 |
| ℓ=512 | 5 | 3,290ms | 258ms | 3,037,125 | 578,367 |
| ℓ=1024 | 1 | 4,108ms | 654ms | 3,002,885 | 542,367 |

ℓ=512 saves 206,192 bytes but regresses verify by 95ms, moving directly away
from the <100ms target. ℓ=1024 saves only another 34,240 bytes while more than
doubling the production verify time and adding ~0.8s prove. Neither approaches
the 700KB target because the unchanged STARK alone is ~2.46MB. Decision: keep
ℓ=256 production and remove the experimental geometries/features; do not carry
dormant profile complexity.

## Production STARK fold-step 3

The unchanged 128-bit production security budget (`pow=20`, `log_blowup=2`,
`queries=54`) supports a FRI fold step of 3. Compared with fold step 2 after the
full-domain Ligero sampler correction, the five-run single-thread result is:

| metric | fold 2 | fold 3 | delta |
|---|---:|---:|---:|
| prove median | 3,252ms | 3,088ms | −164ms |
| verify median | 163ms | 162ms | −1ms |
| proof bytes | 3,243,317 | 3,228,709 | −14,608 |
| FRI proof bytes | 71,956 | 59,668 | −12,288 |

This is a production Pareto win, so `mdoc_production_pcs_config()` now uses
`FriConfig::new(1, 2, 54, 3)`. The verifier pins the exact config. The published
TS13 tuple now also includes `pcs_fold_step=3`; its canonical hash is repinned to
`5445c650a6f57d6be268e1d1b1d98355dddb8188c8496c5e6cffe8da0d4f21e6`.
The tuple/hash suite, exact full TS13 proof, stale fold-step-2 and pre-rebalance
config rejection, and carried-instance tamper rejection all pass in release.

## WO-C1b redundancy argument

**Change:** deleted the `c6` scalar-bits claim family from the EC coprocessor
ECDSA circuit (`crates/eu-id-ec-coprocessor/src/ecdsa.rs`), compacted the
witness layout (removed `LayoutSlot::ScalarBits`, `LAYOUT_LEN` 2680 → 2168),
and dropped the now-orphaned `c3↔c6` u-scalar cross-family binding.

### Why c6 was redundant (verified against the code before deletion)

1. **What c6 asserted.** `build_c6_scalar_bits_circuit` (old ecdsa.rs:4336)
   proved (a) booleanity `bitᵢ² − bitᵢ = 0` for all 512 committed bits and
   (b) decomposition `Σ bitᵢ·2ⁱ = u1` (`C6_U1_INDEX`) and `= u2`
   (`C6_U2_INDEX`). The recompose outputs (indices 512/513) were terminal
   sumcheck outputs of c6 alone.

2. **The bits fed nothing else.** `c6_scalar_bits_input` (old ecdsa.rs:4394)
   was the *only* reader of `LayoutSlot::ScalarBits` (106..618) anywhere in the
   repo (exhaustive grep: the region is written by `write_scalar_bits` in
   `generate_witness` and read only by c6). The scalar-mult ladder is built
   from native `u1_words`/`u2_words` in `write_ladder_accumulators`
   (ecdsa.rs:444-452), not from the bits; its endpoints feed c11/c12/c13/c14-c15.

3. **c6's only cross-family output was redundant.** c6's u1/u2 (read from
   `LayoutSlot::UScalars`) were compared to c3-c5's u1/u2 via
   `verify_u_scalar_cross_family` — the single consumer of the c6 claims. Both
   families read the same `UScalars` slot, so the check only reconciled two
   committed copies of the same logical value.

4. **c3-c5 independently pins the stronger range fact.**
   `c3_c5_scalar_setup_input` (ecdsa.rs:4306) enters z,r,s via
   `Fp::from_bytes_be` (canonical, `< p`), and the c3-c5 layer constrains
   `u1 = z·s⁻¹ − q1·n` and `u2 = r·s⁻¹ − q2·n` (mod p). u1/u2 are base-field
   elements, so they are `< p < 2²⁵⁶` by construction — a range fact at least as
   strong as c6's `Σ bit < 2²⁵⁶`.

**Conclusion.** Deleting c6 removes (a) a booleanity/decomposition proof over
committed values consumed nowhere and (b) a redundant equality between two
committed copies of u1/u2 whose canonical range is already established (more
strongly) by c3-c5. The accepted `(z, r, s, Q)` set is provably unchanged. The
separate, pre-existing "ladder scalar unconstrained" gap is untouched: c6 never
bound the ladder's `u_words` to u1/u2 (only `bits → u1/u2`), so its removal
neither creates nor closes that gap.

Both sides of the deleted c3↔c6 binding were removed (mirroring the E1b
c9/c10↔c12 deletion): the c3 u-scalar consistency pins were dropped along with
all of c6, keeping the prover/verifier consistency cursor balanced.

### Numbers (RAYON_NUM_THREADS=1, BENCH_ITERS=5, ts13_full_probe, M-series)

| metric | before (730e9294) | after (WO-C1b) |
|---|---|---|
| committed_values (full N=1 tuple) | 31,121 | 27,920 |
| prove_ms_median (full) | 2,913 | 2,794 |
| verify_ms_median (full) | 265 | 240 |
| proof_bytes (full) | 4.52 MB | 4.44 MB (4,437,709) |
| proximity_openings bytes | — | 704,712 (+265,416 root_B) |
| claim_batch bytes / prove ms | — | 24,680 / 46.9 ms |
| bundle entry_count (3 ECDSA + MAC) | 25 | 22 |
| ECDSA family count | 8 | 7 |

committed_values dropped 3,201 (WO estimate was −3,141 for the c6 instance
input+pad ×3; the extra ~60 is the dropped c3/c6 u-scalar consistency pins).
Verify stays under the 280 ms bound. STARK side and preprocessed roots untouched
(the coprocessor witness layout is independent of the stwo preprocessed trace).

### Tests

- `cargo test --release -p eu-id-ec-coprocessor` green (47 incl. ignored
  full-bundle negatives; only pre-existing failure
  `gates::g4_gate_count_is_recorded_and_below_mailbox_gate`, missing inventory
  file, unrelated).
- `cargo test --release -p eu-id-prover` green incl. ignored end-to-end forgery
  negatives (`nonce_signature_proof_rejects_wrong_nonce`,
  `identity_with_nonce_flow_rejects_wrong_device_key/nonce`,
  `value_equality_element_identifier_anchor_offset_rejects_in_proof`).
- The c6 splice negative was repointed to a new `spliced_c11` negative (c11 had
  no splice test before), preserving one splice/tamper negative per remaining
  family boundary. Entry-count assertions updated 8→7 / 17→15 / 25→22.
