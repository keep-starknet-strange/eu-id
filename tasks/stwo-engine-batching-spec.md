# stwo engine work — unlock `bound = log_size + 2` for FrameworkComponents

Spec for an agent working on the stwo fork (`github.com/0xLucqs/stwo`,
local clone `/Users/lucas/stwo`; the consumer pins rev `72b638e7` in
`/Users/lucas/eu-id/.claude/worktrees/mldsa-claude-perf/Cargo.toml`).
Written 2026-07-12, at the end of the eu-id PQ perf campaign
(`tasks/keccak-service-design.md` has the full campaign record).

## 1. Why (measured payoff)

The eu-id quantum-safe mdoc proof is floored at **2.20 MB / 4.84 s
single-thread** against targets <1 MB / <1 s. The binding engine
constraint: every `FrameworkComponent` in the fork's lifted composition
must declare `max_constraint_log_degree_bound() == log_size + 1`
EXACTLY. At that bound the constraint-degree budget is D≤3, so the
maximum legal LogUp batch is **pairs** (`finalize_logup_in_pairs`) —
and LogUp interaction columns are 6.4k of the proof's 11.7k committed
columns.

Unlocking `log_size + 2` (D≤5 ⇒ LogUp batch 4) measured/projected:
- interaction columns roughly halve: −3.2k cols ≈ **−460 KB** of
  queried values at 36 queries (and −~2 M cells of tree2/LDE work —
  the S3b experiment measured tree2-commit 5.3 s → 2.7 s at batch 4
  before the OODS failure killed it);
- combined with consumer merging + a blowup-4/27-query schedule this
  reaches the ~0.9–1.0 MB proof target (arithmetic in
  `keccak-service-design.md` §S5).

## 2. Measured failure modes (do not re-derive — reproduce, then fix)

All measured on the eu-id side at rev `72b638e7`, single-thread:

**F1 — bound `log+2` with UNCHANGED constraints fails at OODS.**
Control experiment (campaign stage S3b): take any working
FrameworkComponent (e.g. `stwo-keccak`'s `keccak_round`), change ONLY
`max_constraint_log_degree_bound()` from `log_size+1` to `log_size+2`,
keep pair batching and every constraint identical. Result:
`prove` fails `ConstraintsNotSatisfied` at the OODS sanity check.
Crucially: **trace-domain `assert_constraints` still PASSES** — the
failure is invisible at the constraint-debug layer. Established
mechanism (earlier repro on an interaction-tree Horner component, then
generalized by the S3b control): the composition-domain doubling
desyncs shifted interaction masks (`next_interaction_mask` offsets) —
the OODS point evaluation of masked columns and the quotient
accumulation disagree about the evaluation domain.

**F2 — the `ExtendToEvalDomain` path panics without stored coefficients.**
With FRI `log_blowup = 1` and a component at `log+2`, prove panics
`"The polynomial's coefficients are not stored"` — the
`EvaluationMode::ExtendToEvalDomain` branch requires coefficient-form
polynomials, which only exist when
`CommitmentSchemeProver::set_store_polynomials_coefficients()` was
called. Today only the stwo-p256 lifting path enables it (see
`store_polynomial_coefficients()` in
`/Users/lucas/eu-id/.claude/worktrees/mldsa-claude-perf/crates/air-core/src/lib.rs`
— the orchestrator enables it for the whole proof if any module asks).

**Working reference:** the stwo-p256 monolith DOES prove with
higher-degree constraints via its lifting path (stored coefficients +
`lifting_log_size`). So the engine can do this — the broken case is
specifically FrameworkComponent-based modules inside the shared
composition raising their bound above `log+1`.

## 3. Where to look

- `crates/constraint-framework/src/prover/component_prover.rs` —
  `EvaluationMode` / `ExtendToEvalDomain`, quotient evaluation domain
  selection, mask-point handling. This is the prime suspect for F1
  (domain/mask desync) and the site of F2's panic.
- The lifted-composition / OODS sampling path (`vcs_lifted`, the
  composition polynomial accumulation, and wherever
  `max_constraint_log_degree_bound` sizes per-component eval domains).
- The consumer-side orchestration lives OUTSIDE the fork in eu-id's
  `air-core` (`prove`/`verify`); its contract: per-module
  `max_constraint_log_degree_bound()`, global twiddle sizing
  `max(bounds) + log_blowup`, `store_polynomial_coefficients()` opt-in.

## 4. Deliverables

**D1 — minimal repro inside the fork.** A test in the stwo repo: two
FrameworkComponents sharing one commitment scheme, one declaring
`log_size+2` with a plain degree-2 constraint set and a `[-1,0]`
interaction mask, pair-batched LogUp. Assert it currently fails
exactly as F1 (and F2 with blowup 1, no stored coefficients). This
pins the bug independent of eu-id.

**D2 — the fix.** Make `bound = log_size + 2` (and ideally `+k`)
correct for FrameworkComponents in the shared composition:
- quotient/OODS evaluation domains consistent with the declared bound
  (fix the mask/domain desync);
- `ExtendToEvalDomain` either works without stored coefficients or the
  framework auto-requires them (clear error otherwise — no silent
  wrong math);
- degree-bound VALIDATION stays: a component whose actual constraint
  degree exceeds its declared bound must still fail loudly.
Soundness note for the reviewer: the composition polynomial's degree
accounting and the FRI degree bound must both reflect the raised
bound; an unsound "fix" that merely silences the OODS check is worse
than no fix. Document the degree accounting in the PR.

**D3 — downstream validation in eu-id** (worktree
`/Users/lucas/eu-id/.claude/worktrees/mldsa-claude-perf`, branch
`feat/mldsa-claude-perf`; do NOT touch `.claude/worktrees/mldsa`):
1. Bump the four `0xLucqs/stwo` git pins in the workspace `Cargo.toml`
   to the fixed rev.
2. Regression first: FULL suite matrix unchanged at `log+1`
   (stwo-keccak, stwo-mldsa, `mdoc_mldsa` under
   `--no-default-features --features "p256,ml-dsa"` AND
   `--features quantum-safe-mdoc`, `credential_pipeline` default,
   `scripts/check-quantum-only-deps.sh`) — all green, all runs
   `RAYON_NUM_THREADS=1 --release`.
3. Then the payoff: switch `keccak_round`, `sponge_v`, and the
   attribute/revocation SHA consumers to LogUp batch 4 with
   `bound = log+2` (per-component; NEVER touch the stwo-mldsa `coeffs`
   component — its interaction-tree Horner accumulator is pinned to
   `log+1` by design), re-run the matrix + the perf gate
   `cargo run -p eu-id-prover --release --no-default-features
   --features "p256,ml-dsa" --example pq_perf_probe`
   (current numbers to beat: prove 4,842 ms / verify 29 ms /
   proof 2,199,425 B), and record the measured deltas in
   `tasks/keccak-service-design.md` §Stage gates.

## 5. Acceptance

- D1 repro committed (fails before, passes after).
- Full stwo fork test suite green.
- eu-id matrix green at old pins-equivalent behavior AND at batch-4.
- Measured: proof ≤ ~1.75 MB after batch-4 alone (−460 KB ± noise),
  tree2 phase visibly down (`AIR_CORE_PROVE_TIMING=1`), verify still
  <100 ms.
- A short degree-accounting note in the fork (why `+2` is sound, what
  invariant previously enforced `+1`).

## 6. Out of scope

Blowup-schedule changes, consumer merging, SHA small-load AIR, coeffs
repack — separate campaign items (`keccak-service-design.md` §S5 floor
arithmetic). This spec is ONLY the engine unlock + its direct batch-4
payoff.
