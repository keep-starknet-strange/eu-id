# mdoc P4b performance work orders (2026-07-06, architect)

Baseline of record (working tree @ 9e1ac686 + Q-025 circle-FFT, `mdoc_perf_probe`,
BENCH_ITERS=3, RAYON_NUM_THREADS=1, release): **prove 1,795 ms, verify 715 ms,
proof 5,264,573 B, max RSS 434 MB.** Decomposition: M31 STARK ≈ 1,082 ms /
1.97 MB; coprocessor 713 ms / 3.29 MB (openings A 2.44 MB + B 0.77 MB);
claim_batch 259 ms, rs_encode 172 ms, sumcheck 122 ms, merkle 77 ms.

Every WO gate is an executable probe/bench command plus a number. No number,
not done. Re-pin discipline: P2+P3 land together (one fixture re-pin); P1 is
byte-identical (no re-pin); P6 is its own re-pin. All soundness/negative gates
from Q-021/Q-024/Q-025 unchanged throughout.

---

## WO-P1 — Circle claim-batch prover restructure

**Goal:** claim_batch_ms 259 → ≤ 150, byte-identical output.
**Owner/effort:** codex, ~1 day. **Deps:** none.

Scope (all in `crates/eu-id-ec-coprocessor/src/ligero.rs` +
`circle_fft.rs`, prover only — verifier and proof bytes untouched):
1. Product in a 512-point domain instead of 2048: add message-tables for a
   size-512 canonic coset (generator order 1024). Per touched row compute
   FFT512(pad(w_coeffs)) ∘ FFT512(pad(row_coeffs)) accumulated into a
   512-length value accumulator (use `coefficient_rows`, not the codeword);
   add blind via FFT512 of its 322 coeffs; ONE IFFT512 at the end → F_322
   coefficients. Per-row mults drop ~17k → ~9k.
2. `batched_row_weights`: replace the per-cell 13-mult eq bit-product with the
   standard O(2^m) tensor doubling per claim, then scatter into row windows.
3. Tail-zero assert stays (now on the 512-vector: entries [322..512) zero).

**Gates:**
- `claim_batch_ms ≤ 150` in the probe.
- Byte-identical `claim_batch.coefficients` on a fixed committed fixture
  (same Q as a function — test comparing old/new path output, then delete the
  old path).
- Full coprocessor suite + ignored release gates green.

---

## WO-P2 — Bulk pad drawing

**Goal:** rs_encode_ms 172 → ≤ 110 (the FFT floor is ~85; pads are ~87).
**Owner/effort:** codex, ~0.5 day. **Deps:** none. **Re-pin:** yes (pad
values change if the squeeze order changes — batch with P3's re-pin).

Scope: `channel.rs`: add `draw_fps(&mut self, n) -> Vec<Fp>` squeezing
ChaCha output in large blocks with in-place rejection sampling.
`ligero.rs::commit_witness_profiled`: draw each row's 192 pads (and mask/blind
rows) via one call. Applies to both `LigeroCode` paths.

**Gates:** `rs_encode_ms ≤ 110`; pads still sourced solely from the
`eu-id-s4-ligero-v2-pad` channel (hiding argument unchanged); suites green;
re-pin recorded.

---

## WO-P3 — STARK pow/query rebalance

**Goal:** proof −≈135 KB for ≤ +30 ms prove.
**Owner/effort:** codex, ~0.5 day incl. re-pin. **Deps:** none.

Scope: the mdoc STARK currently proves with `PcsConfig::default()`
(pow_bits 10, n_queries 59, log_blowup 2 ⇒ 59·2+10 = 128 bits). Build an
explicit config: **pow_bits 20, n_queries 54** (54·2+20 = 128, unchanged
security). Set it at the prove site ([mdoc.rs:3362] config field) and in
`expected_pcs_config` (verifier pin — must reject the old config).

**Gates:** `byte_breakdown.stark.queried_values ≤ 1.49 MB`;
`prove_ms_median` within +30 ms of baseline; verifier rejects a proof made
with the old config (negative); re-pin.

---

## WO-P4 — Merkle/channel hasher bake-off (measure only, no landing)

**Goal:** decision data for parity-plan §3.4; commits are ~17% of STARK prove
+ 77 ms coprocessor merkle.
**Owner/effort:** codex, 1–2 days. **Deps:** none. **Landing:** BLOCKED on
Lucas + recursion-roadmap decision (recursion AIR assumes Blake2s).

Scope: ignored bench over the real tree shapes (stwo Merkle at mdoc sizes;
coprocessor `merkle.rs` at 4096×147-ish): Blake2s (current) vs Blake3 vs
hardware SHA-256 (ARMv8 crypto ext). Report ms/tree and projected probe delta.

**Gates:** bench table in perf-log with all three measured, single-thread.
No production change in this WO.

---

## WO-P5 — SHA-table cell inventory + merge round

**Goal:** `shape_cells` 8.16 M → ≤ 7.0 M; probe prove −≥150 ms; queried_values
shrinks proportionally. `mdoc_sha_tables` alone is 5.11 M cells (fixed cost).
**Owner/effort:** codex phase 0, architect ranking, codex impl; 3–5 days
total. **Deps:** none (independent of P1/P2/P6).

Phase 0 (half day, gate for the rest): extend the probe module dump to emit
per-module preprocessed/trace/interaction cells AND per-component column
counts × log sizes. No analysis without this.

Phase 1 (architect, via mailbox): rank candidate reductions. Known candidates
to price — do NOT pre-commit to any: (a) split-pack/sigma table keyed
consolidation (fewer, taller tables — may be net-negative, price it);
(b) multiplicity column packing; (c) maj_ch group width 6→5 (2×2^18 → 2×2^15,
but partition fan-out changes — price trace growth); (d) WO-3.2-style dust
merge across the small bind modules (~30 K cells, low value, do last if at
all). Each candidate gets a predicted cell delta before implementation.

Phase 2: implement top-ranked items one at a time; per item gate:
predicted-vs-measured cells within 15%, prove delta ≥ predicted × 0.5, else
revert that item. Full negative suite after each.

**Gates:** `shape_cells ≤ 7.0 M`, `prove_ms_median ≤ baseline − 150 ms`,
`queried_values` reduced, all suites + SHA KATs green.

### Phase 1 ranking (architect, 2026-07-07, from the phase-0 dump)

Dump facts: shape_cells 8,161,328. mdoc_sha_tables 5,112,096
(interaction/log16 36 cols = 2,359,296; preprocessed/log16 33 cols =
2,162,688; trace/log16 9 cols = 589,824). Per-stream SHA interaction:
issuer 1,784 cols/log9 = 913,408; birth 272,384; nat 249,856; device
69,632 (Σ = 1,505,280).

Ranked queue — implement in this order, one at a time, per-item gate =
predicted-vs-measured cells within 15% AND prove delta ≥ predicted × 0.5,
else revert that item:

- **R1 — STRUCK (verified 2026-07-07): already pairwise-batched.**
  Per-stream SHA consumers batch 66 entries/row → 33 SecureField cols in
  `build_interaction_columns` (stwo-sha256/src/interaction.rs:~200-245,
  explicit `n0·d1 + n1·d0 / d0·d1` pairing). No savings left here.
- **R0 (NEW, first) — per-component `component_shapes()` accessor** (the
  phase-0 scope note): small read-only accessor on the mdoc module traits
  + probe extension. Unblocks R2-verify, R4 pricing, R5 pricing. Half a
  day, byte-identical.
- **R2 — producer-table fraction batching: verdict UNRESOLVED.** The
  sweep's claim "12 producer lookups → 6 pairs" contradicts its own
  finding that each producer component calls
  `build_interaction_columns(log_size, vec![frac])` with ONE fraction —
  single-fraction calls cannot pair, and fractions cannot pair across
  components. The dump's 36 base cols (= 9 SecureField) at log16 is
  consistent with UNBATCHED single-fraction producers. If unbatched, the
  fix is component-level: co-locate same-log16 producer tables in one
  component so their fractions pair (also shares multiplicity plumbing —
  subsumes part of R3). Predicted IF unbatched: interaction 36 → ~20 base
  cols ⇒ **−1.0 to −1.05 M** cells. Verify with R0 before implementing.
- **R3 — multiplicity column packing (WO candidate b)** across the log16
  tables (trace 9 cols → ~5). Predicted **−0.2 to −0.3 M**. Partly
  subsumed by R2's component co-location if that lands.
- **R4 — maj_ch width 6→5 (WO candidate c): BLOCKED on R0.** The dump
  shows NO log17/log18 buckets — the WO's "2×2^18" shape does not exist
  in this tree. Do not implement blind.
- **R5 — keyed split-pack/sigma consolidation (WO candidate a): likely
  NET-NEGATIVE** (k tables → 1 adds ⌈log2 k⌉ key bits ⇒ taller table
  outweighs saved columns at k ≥ 4). Price only after R0; expect to
  strike.
- **R6 — dust merge (WO candidate d): SKIP** (~30 K cells).

Phase-2 sequencing: R0 → R2-verify (+implement if unbatched) → R3 → gate
check. Degree audit per item (D≤3, log+1 rule). **Honesty note:** with R1
struck, the ≤ 7.0 M gate is reachable only if R2 is real (~−1.0 M) plus
R3; if R2 turns out batched after all, the remaining lever is the
preprocessed side (2,162,688 cells at log16) = the content-aware table
redesign, which is decision **D-2** (Lucas/architect), not a phase-2
item — report and stop rather than force it.

---

## WO-P6 — Ligero aspect-ratio re-sweep (ℓ = 128)

**Goal:** proof −≈1.6 MB (openings 3.21 → ~1.6 MB). CORRECTION to the earlier
analysis: encode does NOT pay ~2.2× — rows halve as ℓ doubles, so total FFT
cost grows only logarithmically; the real prove cost is the ℓ² weight
interpolation (~+75–100 ms net). **Deps: land after P1** (P1's restructure
halves that cost class and the margin exists after P2/P5).
**Owner/effort:** codex, 2–3 days + param review by architect. **Re-pin:** yes.

Scope:
- New `v3_circle_params()`: row_len 128, degree_bound 512 (keep rate 1/8),
  codeword_len 4096, claim bound = 512+128+2 = 642, proximity_radius
  e ≤ (4096 − 642 − 1)/2 = 1726, openings t: re-derive — e/n ≈ 0.4214 (same
  ratio as today) ⇒ t ≈ 170 (recompute exactly via `soundness_error`, assert
  ≤ 2^-132 in a test, record the derivation in the WO report).
- `circle_fft.rs`: parametrize the data window (128 slots), message domain
  D512 (generator order 1024), codeword domain D4096 (order 8192), M128⁻¹.
  Pad budget = 512 − 128 = 384 ≥ t = 170 ✓.
- `ligero.rs`: nothing structural — the Q-025 dispatch is already
  size-generic except the hardcoded CIRCLE_* consts; lift them into params-
  derived lookups keyed by `LigeroCode` variant or a params-carried size.
- Assess ℓ=256 in the same sweep ON PAPER only (predicted −2.4 MB total,
  +250–400 ms from ℓ² interpolation unless P1's FFT-based weights land);
  report, don't build.

**Gates:** `proof_bytes ≤ 3.7 MB`; `prove_ms_median ≤ pre-P6 + 120 ms`;
soundness_error test ≤ 2^-132 with the new params; verifier rejects old-params
proofs (config pin negative); FULL negative suite incl. both compensating-
forgery tests; re-pin.

---

## WO-B0 — CANCELLED (2026-07-06, Lucas)

**Decision: stwo is the proving engine for the hash side — a product
constraint, not a perf question.** Path B's endpoint removes stwo from the
mdoc proving path, so the spike's number could never be acted on; do not run
it, do not resurrect it on perf grounds alone. Path A (P1–P6) is the strategy
of record; its ceiling (~1.25–1.45 s single-thread, ~3.1–3.3 MB) is accepted.
If the *final-proof-is-stwo, inner-flexible* (recursion) reading ever becomes
the requirement, that is a NEW decision — re-open as a recursion feasibility
spike, not as this WO. P4's hasher choice should still note recursion-
friendliness as a tiebreaker.

<details><summary>Original B0 scope (kept for the record)</summary>

## WO-B0 (original) — Boolean-sumcheck SHA kill-switch spike (decision gate for Path B)

**Goal:** the ONE number that decides whether prove parity is fundable: ns/term
for an uncommitted-wire layered sumcheck proving SHA-256, single-thread.
**Owner/effort:** codex under architect supervision, 1 week, scratchpad crate
(pattern: `scratchpad/gkr-bench` from parity S3). **Deps:** none — parallel to
all P-items. **Non-goals:** ZK, Ligero integration, transcripts, production
code, multi-block.

Scope: one SHA-256 compression block as a layered quadratic circuit
(~30–60 K gates) in TWO encodings: (a) M31 bit-per-wire, (b) GF(2^128)
packed-XOR (Longfellow-style; XOR = add). Prove the layer reduction with a
minimal dense sumcheck inner loop (plain quadratic gates — no LogUp fractions),
NEON, single-thread. Measure best-of-3 ns/term and terms/block.

**Pre-registered decision rule** (write it in the report before measuring):
projected mdoc SHA side = ns/term × terms/block × block-count(fixture) +
input-commit estimate.
- **GO** (fund Path B design): projection ≤ 350 ms single-thread M-class
  (≥3× vs the 1,082 ms STARK side, with engine-risk margin).
- **NO-GO:** Path A is the ceiling; write the posterity note next to the
  parity Q-025/Q-028 notes and close the direction.
Decision is Lucas's either way — the spike only produces the number.

</details>

---

## STATUS 2026-07-07 (architect) — first wave landed

- **WO-P2 DONE with premise correction.** `draw_fps` bulk squeezing landed
  (channel.rs + all four commit sites). Measured pad cost was **~16 ms**, not
  the WO's ~87 ms (that split predated the circle tree): rs_encode 179 →
  162–167 ms (median of 3). The ≤110 gate is UNREACHABLE by pad work — the
  residual ~150 ms is the per-row FFT2048 itself. Gate re-scoped: rs_encode
  reduction now rides on P6 (fewer, wider rows) / FFT kernel work, not pads.
- **WO-P3 DONE.** `mdoc_production_pcs_config()` → pow_bits 20 / n_queries 54
  (128-bit unchanged); verifier pin enforces it; negative
  `rejects_old_pcs_config_after_pow_query_rebalance` green. proof_bytes
  5,264,557 → **5,119,301** (−145 KB, beats the −135 KB goal); queried_values
  1,545 KB → **1,487,856 B ≤ 1.49 MB** ✓; prove flat (+30 ms budget unused).
- **Re-pin: N/A — no byte-pin exists.** Pads are OsRng-seeded
  (`fresh_pad_channel`), proof bytes non-deterministic by design; all tests
  use dynamic roots. The "re-pin" lines in P2/P3/P6 are void until a fixture
  pin exists (tracked separately in remaining-work-orders WO-5 step 7).
- **WO-P5 phase 0 DONE.** Probe emits per-module + per-column-group cells,
  additive JSON, byte-identical. shape_cells **8,161,328**; mdoc_sha_tables
  **5,112,096** (63%), of which interaction/log16 2,359,296 +
  preprocessed/log16 2,162,688. Phase 1 ranking is next (architect).
- **WO-B0: ran to completion BEFORE the cancellation edit was seen** (launched
  under the original doc's "immediate, parallel" sequencing). Result kept as
  the posterity note only: M31 SIMD 7.66 ns/term, 178,638 terms/block,
  ~140–240 ms projection (conditional GO indication) —
  tasks/parity/B0-sha-sumcheck-spike.md. **Moot per the cancellation; no
  action taken or planned.** `scratchpad/sha-sumcheck-spike/` is disposable —
  delete at will.
- A-004 ignored negatives fail identically before/after (pre-existing,
  tracked as promotion gate).
- Combined-tree verification (probe + coprocessor suite) green on the shared
  working tree @ 9e1ac686.
- **WO-P1 DONE (verified 2026-07-07).** D512 product domain
  (`CIRCLE_PRODUCT_DOMAIN_LEN=512`, `circle_product_fft/ifft`), `eq_tensor`
  tensor-doubling weights, tail-zero gate on the 512-vector; byte-identity
  test `circle_claim_batch_d512_matches_2048_reference` (single + split
  paths) green. **claim_batch_ms 272 → 114** (gate ≤ 150 ✓); full
  coprocessor suite green (112 tests); queried_values unchanged 1,487,856;
  proof size class unchanged. (Impl agent hit its session limit before
  reporting; gates re-run and verified by the architect.)
- **Incident 2026-07-07: `/private/tmp/stwo-dev-copy` deleted by tmp
  cleanup** — the workspace Cargo.toml (COMMITTED, lines 42-43) path-patches
  stwo into /tmp. Restored via
  `git -C /Users/lucas/stwo worktree prune && git -C /Users/lucas/stwo
  worktree add /private/tmp/stwo-dev-copy dev-copy` (tip 72b638e7, matches
  WO-S4's pinned fix). All suites green post-restore. The /tmp location is
  a time bomb — separate fix task filed (move the worktree to a durable
  path or vendor the fork).
- Post-P1 headline (BENCH_ITERS=1, single run): **prove_ms_median 1,788 /
  verify 683**; phases: witness_check 49, circuit_build 35, rs_encode 193
  (166 at median-of-3), merkle 85, sumcheck 128, claim_batch 116. The M31
  STARK side (~1.08 s) is now the dominant cost — P5 phase 2 is the lever.
- **WO-P6 DONE (2026-07-07, all gates green).** v3 params (ℓ=128,
  k=512, n=4096, claim 642, e=1726, **t=168 exact** — WO guessed 170;
  soundness **2^-132.61**, test-pinned). `CircleGeom` parametrization
  (L64/L128 coexist), production path v2→v3 at ecdsa.rs
  `implemented_circuit_ligero_params`, config-pins at ecdsa.rs:1255/1506
  reject v2 bundles + new `v3_verifier_rejects_v2_params_batch`.
  **proof_bytes 5,118,117 → 3,604,953 (−1.51 MB; openings 3.21 → 1.67
  MB)**; prove_ms_median 1,872 (budget 1,908 ✓); rs_encode 204 /
  claim_batch 164 (ℓ² interpolation growth, as priced); suites 116+36+21
  green incl. both compensating-forgery tests. ℓ=256 paper assessment:
  ~2.77 MB projected, +50–100 ms — not built, revisit only if size
  pressure returns.
- **Cumulative vs the WO baseline of record:** prove 1,795 → **1,872 ms**
  (net ~flat: P1/P2/P3 savings traded for −1.66 MB), proof 5,264,573 →
  **3,604,953 B (−32%)**, verify unchanged-informational. Remaining prove
  lever = P5 phase 2 (M31 STARK side ~1.08 s dominates).
- **P5 phase 1 ranking written below (R0, R2–R6; R1 struck as
  already-batched).**
- **WO-P5 phase 2 DONE (2026-07-07).** R0 accessor landed (true
  per-component probe rows, byte-identical). **R2 verdict: UNBATCHED**
  (each producer table emitted one unpaired fraction column —
  shared_tables.rs:436/470/502 pre-change); fixed by co-locating same-log
  producers into `SharedProducerPairEval` components (MajChEval pattern):
  interaction cols log16 36→20, log4 12→8, **cells −1,048,640 (predicted
  −1.0…−1.05 M, exact hit), prove −227 ms**. R3 skipped per its own hedge
  (distinct dense multiplicity vectors; packing needs new demux
  constraints, net-negative). **shape_cells 8,161,328 → 7,112,688** —
  0.11 M above the ≤7.0 M gate; the residual is the preprocessed side
  (2,162,688 cells/log16) = **decision D-2**, out of phase-2 scope.
  Suites all green (stwo-sha256 143, prover 57, coprocessor untouched);
  no NEW A-004 failures.
- **Post-phase-2 headline (BENCH_ITERS=3): prove_ms_median 1,742 /
  verify 783 / proof_bytes 3,601,593 / queried_values 1,483,376.**
  Cumulative vs the baseline of record: **prove 1,795 → 1,742 ms (−3%),
  proof 5,264,573 → 3,601,593 B (−32%)**, cells 8.16 → 7.11 M.
- **WO-P4 DONE (2026-07-07, measure-only).** Kernel-replay over the real
  tree shapes (STARK trees 1,572,861 hashes / 115.3 MB; coproc Ligero v3
  4096×219 = 8,191 hashes / 29.2 MB), best-of-3 single-thread:
  Blake2s 235–245 + 44–48 ms; Blake3 164–171 + 23–25 (**≈ −126 ms
  projected**); hardware SHA-256 75–81 + 12–13 (**≈ −253 ms projected**,
  2.0–2.2 GB/s confirmed ARMv8 crypto ext). Bench:
  eu-id-ec-coprocessor/tests/hasher_bakeoff.rs (#[ignore]); table in
  perf-log. Recommendation (input, not decision): SHA-256 dominates on
  both raw win and in-repo-AIR recursion-friendliness; sole blocker is
  the Blake2s-specific recursion AIR. **Landing blocked on Lucas +
  recursion roadmap, as scoped.**
- **GATE CHANGE (Lucas, 2026-07-07): verify IS now a gate — ≤ 200 ms**
  ("under 200 ms felt instant; ~800 is too much"; revises the Q-024
  re-weight). Measured breakdown: verify 764 = claim_batch verifier 674
  (88%) + setup 30 + sumcheck 25 + proximity 14 + ~20.
- **WO-P7b DONE (2026-07-07) — verify gate PASS in multi-thread posture:
  158 ms ≤ 200** (claim_batch 200 → 66 on 12 cores; rayon over the 168
  independent column checks + the basis/fold precompute, deterministic
  index-ordered collect). Lever 1 (Fp::sum_of_products lazy reduction)
  NOT VIABLE without forking: `Fp` wraps `p256::FieldElement` 0.13.2
  whose Montgomery limbs are `pub(crate)` — no public limb access, no
  sum_of_products; reported and skipped per scope. Consequence:
  **single-thread verify stays ~291 ms** — the phone-verifier posture
  cannot reach 200 without a field-crate fork/vendor (potential future
  WO-P7c, Lucas's call). Prove untouched (~1,724 within noise, rayon not
  entered at 1 thread); proof ~3.59-3.60 MB unchanged; all negatives +
  byte-identity + suites green; rayon dep added to the coprocessor crate
  (workspace convention). **Verifier posture decision → Lucas: server
  verify 158 ms ✓; on-device verify 291 ms unless P7c is funded.**
- **WO-P7 DONE-PARTIAL (2026-07-07) — big win, ≤50/≤200 gate NOT reachable,
  STOP as scoped.** Design B: per-opened-column universal-basis precompute
  (`CircleColumnBasis`, tensor-doubling, O(len) mults) + weight-inverse fold
  (`fold_weight_inverse` bakes M⁻ᵀ into each column basis so a row's raw
  weights evaluate in ONE dot, no per-row `circle_weight_coeffs`). New
  `ClaimBatchColumnEval` replaces the per-(row,column)
  `circle_evaluate`/`circle_weight_coeffs` recompute in BOTH
  `verify_claim_batch` and `verify_split_claim_batch`. Chose B over A:
  A's per-row FFT4096 (~20 M mults) and ~27 MB transient both lose to B's
  ~8.75 M mults / ~4 MB. Files: circle_fft.rs (+`CircleColumnBasis`,
  `fold_weight_inverse`, tests), ligero.rs (verifier fns +
  `ClaimBatchColumnEval`; `weight_evaluations` now RS-only). Prover paths
  byte-untouched. **claim_batch verify 674 → 194 ms (−71%); verify total
  783 → 283 ms (−64%)**; prove 1,742 → 1,724 (noise, no prover change);
  proof_bytes ~3.60 M unchanged; peak transient +~4 MB. Gate ≤50/≤200 NOT
  met — the residual is the information floor of the check: a 99.9%-dense
  `openings(168) × rows(281) × data_slots(128)` ≈ 6.0 M Fp-mul contraction
  (weight_evals 109 ms) + M⁻ᵀ fold precompute 2.75 M ≈ 54 ms, at
  ~18 ns/Montgomery-mul (p256 FieldElement, no `sum_of_products`). No
  rearrangement (fold, reorder-to-matmul V=WᵀCol, per-claim, sparsity)
  drops below ~157 ms without changing frozen P6 params
  (openings/rows/data_slots). Byte-identity gate
  `circle_claim_batch_byte_identity_v2_and_v3` + `column_basis_matches_
  circle_evaluate` green; old circle eval path deleted (no dead code). All
  suites green (coprocessor 31 lib + 23 ignored incl. both compensating-
  forgery negatives + `v3_verifier_rejects_v2_params_batch`; prover
  mdoc_support 36, lib 21). Reaching ≤50 needs a protocol change (fewer
  openings, or a non-interpolated weight functional) — out of this
  verifier-only WO's scope.
- **WAVE COMPLETE.** All queue items dispositioned: P1 ✓, P2 ✓(premise
  corrected), P3 ✓, P4 ✓(measured), P5 ✓(R2 landed; 7.11 M vs ≤7.0 M
  gate — residual is D-2), P6 ✓, B0 ran-then-cancelled (posterity note).
  Everything UNCOMMITTED in the working tree on top of 9e1ac686; commit
  grouping is Lucas's call. Open decisions: D-2 (preprocessed/SHA-floor
  redesign — the last 0.11 M cells + the next prove lever), P4 hasher
  landing, ℓ=256 (paper: ~2.77 MB, +50–100 ms), plus D-1/D-3..D-6 in
  tasks/remaining-work-orders-2026-07-06.md.

---

## Sequencing & projected endpoint

Immediate, parallel: **P2+P3** (one re-pin train), **P5 phase 0**.
Then: **P1** (byte-identical) → P5 phase 1/2 → **P6** (needs P1 + margin).
P4 measurement whenever; landing decision separate (recursion-friendliness is
a tiebreaker per the B0 cancellation note).

Projected endpoint (sum of gates, conservative):
**prove ≈ 1.25–1.45 s** single-thread M-class (≈ 4.0–4.6 s Pixel-9 1-thread,
≈ 2.0–2.3 s at the 2× mobile threading budget), **proof ≈ 3.1–3.3 MB**,
verify unchanged (informational). Longfellow marks: 931 ms / 291 KB — this
lands ~2× prove / ~11× size, accepted as the ceiling per the B0 cancellation
decision (stwo-is-the-engine constraint).
