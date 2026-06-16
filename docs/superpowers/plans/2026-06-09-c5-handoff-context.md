# C5 Soundness Build — Handoff Context for the Continuing Agent

**You are continuing a soundness build on the `stwo-p256` crate (a P-256 ECDSA verification STARK AIR, `stwo` framework) on branch `lucas/p256`.** Read this whole document first — it is self-contained. The companion plan is [`2026-06-09-c5-ladder-ec-arithmetic-soundness.md`](2026-06-09-c5-ladder-ec-arithmetic-soundness.md) (the **B2 + Option A** sections are LIVE; the **AFFINE PIVOT** section is ABANDONED — ignore it). The audit of record is `crates/stwo-p256/docs/soundness-audit.md`.

---

## Mission

A soundness audit found three live-path ECDSA forgeries in this AIR:
- **C1** — free correction digit in the Solinas Fp modular reduction (every Fp multiply forgeable). **DONE.**
- **C2** — unconstrained top product-chunk digit in `scalar_mod_mul` (s·u1 / s·u2 reductions forgeable). **STILL OPEN — out of scope here.**
- **C5** — the fake-GLV EC scalar-mul **ladder is unconstrained**: nothing forces each ladder step's `output = rcb_double/rcb_mixed_add(inputs)`. R = u1·G + u2·Q forgeable. **PARTIALLY DONE** (ladder steps constrained; prepared-table inputs not yet).

**Your job: finish C5.** Two tasks (details in "Remaining work" below):
- **Task A — Prepared-table source formula** (the real remaining soundness gap).
- **Task B — Forgery-test hardening** (regression protection for the already-sound bindings).

---

## What is already DONE (committed on `lucas/p256`, suite 305 passed / 0 failed / 10 ignored)

| Commit | What |
|---|---|
| `986ce32` + `ab48dcc` | **C1 closed.** `correction_product_digit` is now pinned to the convolution of nine Range13-checked 13-bit `correction_digit[i]` + a sign bit (`field/solinas/air.rs`). Soundness-reviewed ✅. |
| `669a8e6` | **C5-1.** `ProjectiveRcbMulResultRelation` (arity 5, keyed `(source_index, mul_index, role, limb)`): the `projective_rcb_mul` "silo" PROVIDES every EC op's per-mul `(lhs,rhs,result)` limbs; the two EC-source consumers CONSUME them. Correctness-reviewed ✅ (the `has_muls` gate is slack-free; the 3-way balance partitions silo rows by `source_index`). |
| `e387c3b` | **Silo 13→15 muls/op.** Added 2 affine-normalization muls per op (M13 `output_affine.x·output_projective.z → output_projective.x`, M14 likewise for y) so the affine output can be bound. `PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP = 15`. |
| `df838bc` | **Double-op formula** (`components/fake_glv/ec_source/double_formula.rs`). Constrains `output = rcb_double(input)` in the ladder source consumer. Soundness-reviewed ✅ (exact transcription, all 30 operands bound, z3≠0 gating airtight via P-256 prime order). |
| `b914d16` | **MixedAdd-op formula** (`components/fake_glv/ec_source/mixed_add_formula.rs`) + the degree-fix gating refactor. Soundness-reviewed ✅. |

**Net:** C1 fully closed. C5's **ladder steps** (both Double and MixedAdd) are now constrained in-AIR and independently soundness-verified; forged ladder outputs are rejected by `verify_current_air_monolithic`.

---

## Architecture you must understand

- **The silo** (`components/projective_rcb_mul/`): proves each EC op's field-multiplications `result = lhs·rhs mod p` via a Solinas reduction (`field/solinas/`). The shared builder is `add_projective_rcb_mul_row` — **also used by `final_add` and `public_key_curve`; do not break it.** The C1 fix lives in its Solinas reduction. Each EC op = **15** mul rows.
- **`projective_ec_trace`** (`curve/projective.rs`, `ProjectiveEcRow`): one row per EC op, holding affine `lhs_affine`/`rhs_affine`/`output_affine` + a `output_projective` (x,y,z). Built `from_native_traces`. The silo proves all of it.
- **Two consumers** read slices of `projective_ec_trace` and (via C5-1) consume the silo's proven muls:
  - **The fake-GLV ladder source** — `components/fake_glv/ec_source/air.rs` (`FakeGlvProjectiveSourceEval`). **This now constrains the coordinate formula** (Task done) via `double_formula.rs`/`mixed_add_formula.rs`.
  - **The prepared-table source** — `components/fake_glv/prepared_table/` (the `PreparedTableProjectiveSource` provider/consumer; balance entry `PreparedTableProjectiveSource` in `proof/mod.rs`). It consumes the muls (C5-1) but **does NOT yet constrain its coordinate formula → this is the remaining hole (Task A).**
- **The formula pattern** (what you reuse): a consumer that has the affine point columns CONSUMES the 15 muls for its op and constrains, gated by op-type:
  1. **operand binding** — each mul's `lhs`/`rhs` limbs = the correct input coord / constant (`1`, curve `b`) / prior mul result `R_k` / committed glue working-value (via `add_combo_reduction`, a signed-carry limb reduction). **Bind operands, not just results** — a result-only binding lets a prover pair a correct product with wrong operands (forgery).
  2. **output projective** — `x3,y3,z3` = the documented linear combos of the `R_k`.
  3. **affine-norm** — `R13=x3`, `R14=y3` (the M13/M14 muls prove `output_affine·z3 = R13/R14`), **gated by a finite-output flag** `out_finite = 1−output.inf` with the per-limb `output.inf·z3.limb=0` non-degeneracy. (For `double(∞)`/infinity outputs z3=0; the gating releases the binding and the infinity case is handled separately.)
  4. **infinity / inactive** — gated off; output forced consistent.
- **Where the result lands:** the ladder's final point reaches `final_check` via `FinalAddOutputRelation` → binds `x(R) mod n = r` (public). Unchanged by this work.

---

## Remaining work

### Task A — Prepared-table source formula (the remaining soundness gap)

The prepared table holds the precomputed multiples of G and Q (`base[0..7]`, `table16`) that the ladder adds. They are **computed natively and only *pinned*** for 3G/R3/canonical (via `PIN_SCHEDULE` in `prepared_table/air.rs`); the **intermediate doublings/additions that build them are routed to the silo but not coordinate-constrained** — the same C5 hole, one layer up. A forger could forge a table multiple, hence forge R, even though the ladder steps are now sound.

**Do this:**
1. **Map the prepared-table source.** Read `prepared_table/air.rs` + `prepared_table/trace.rs`. Identify the EC ops it performs (the design notes call them `DoubleP`, `AddP2P`, `DoubleR`, `AddR2R`, `Base`, `Table16`) and which are genuine arithmetic vs. fully pinned (no arithmetic — those need no formula).
2. **Apply the formula** to the prepared-table source consumer the same way `ec_source` does — **reuse `double_formula.rs` / `mixed_add_formula.rs`** (their binders are `pub(crate)`). The consumer already consumes the 15 muls (C5-1); add the coordinate-formula constraints.
3. **Watch the coordinate system.** The ladder's inputs are affine with **z1 = 1** (the MixedAdd transcription in `mixed_add_formula.rs` assumes this). Prepared-table ops may chain **projective** intermediates (z ≠ 1) — re-derive the transcription from `rcb_double_with_mul_rows`/`rcb_mixed_add_with_mul_rows` for the prepared-table operands if their inputs are not affine-z1. **Do not assume the ladder's z1=1 transcription transfers unchanged.**
4. **Verify:** monolithic proof proves+verifies; relation audit balanced + fully linked; a forged prepared-table multiple is rejected.

### Task B — Forgery-test hardening (regression protection)

The ladder-op forgery tests (`current_p256_monolithic_rejects_forged_double_op_output`, `..._mixed_add_op_output`) forge the affine `output`, which trips the **pre-existing** EC-row LogUp relation (`RelationImbalance{FakeGlvProjectiveSource}`) — so they **would pass even if the new coordinate-formula bindings were deleted.** The bindings ARE sound (verified by the math reviews), so this is regression protection, not a soundness defect.

**Add binding-isolation tests:** forge something that **only** the new coordinate-formula constraints catch — e.g. a committed working value (`x3`/`y3`/`z3`), a reduction carry, or a silo mul *operand* with the EC-row output left consistent. Because these are **polynomial** constraints (not LogUp relations), `verify_balanced` will NOT catch them — use a **component-level recording-`EvalAtRow` harness** (copy the pattern from the C1 test `solinas_reduction_rejects_forged_correction_product_digit` in `projective_rcb_mul/tests.rs`, which exists precisely because `assert_constraints` double-panics).

---

## Critical gotchas (these cost hours — read them)

1. **DEGREE ≤ 2 (SubDomain mode) — the big one.** The monolithic proof runs every component at `max_constraint_log_degree_bound = log_size + 1`, i.e. constraints are quotient-ed at **degree ≤ 2**. A constraint of degree > 2 whose factors are **not zeroed off-row** ALIASES in the composition → `ProvingError::ConstraintsNotSatisfied` **for valid proofs** (a completeness break). Crucially, **`assert_constraints_on_trace` does NOT catch this** (it only checks trace rows; the failure is in the OODS composition). **Bumping the degree bound does NOT fix it.** The fix: **witness any multi-factor gate as a degree-1 committed column** (constrained equal to the product), so bindings stay degree 2. See `mixed_add_formula.rs`'s `mixed_active_col` / `formula_gate_col`. (Double's degree-3/4 constraints survive only because their factors `x3,y3,z3` are zeroed off-Double, giving extra vanishing — don't rely on that; witness the gate.)
2. **`rtk git` munges arguments** — it stages untracked files with `-u` and rejects multiple `-m`. **Use plain `git`** for staging/commits; stage your specific files explicitly.
3. **Tests are RELEASE-mode and SLOW** (tens of seconds to several minutes each; the full `proof::tests` is ~30 serial proofs and can take 15+ min). Always: `rtk proxy cargo test -p stwo-p256 <name> --release -- --test-threads=1 --nocapture`. Be patient — not a hang.
4. **`assert_constraints` double-panics** (`LogupAtRow::drop` → SIGABRT, uncatchable by `catch_unwind`) on a failing row. For component-level forgery tests use a **custom recording `EvalAtRow`** that records constraint values instead of asserting zero (pattern in `projective_rcb_mul/tests.rs`).
5. **No `Co-Authored-By` line in commits** (user's standing instruction).
6. **Soundness discipline:** transcribe EC formulas EXACTLY from `curve/projective.rs` (`rcb_double` :242, `rcb_mixed_add` :285); validate numerically over real P-256 if unsure. Bind mul **operands**, not just results. After each new formula, get an **independent soundness review** (re-derive the transcription, check operand-binding completeness, infinity cases, gate-column identity preservation, and that every reduction carry is range-checked — an unconstrained carry is the C1 forgery class). Do not trust a passing test as proof of soundness.
7. **The √n range checks are NOT needed** here — that was an *affine-ladder* requirement (an approach that was explored and abandoned). The projective RCB approach is unconditionally complete.
8. **Degree of `add_combo_reduction`:** it's degree 1 in committed columns × the gate you pass. Pass a degree-1 (witnessed) gate to keep the constraint at degree 2 (gotcha #1).

---

## Verification gates (run after each task; release mode)

```bash
rtk cargo check -p stwo-p256 --tests
rtk proxy cargo test -p stwo-p256 monolithic_relation_audit_is_balanced_and_fully_linked --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 current_p256_proof_pipeline_proves_and_verifies_current_air_monolithic_proof --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 current_p256_proof_pipeline_proves_and_verifies_monolithic_distinct_branch --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 current_p256_monolithic_proves_arbitrary_doubling_final_add --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 width --release -- --test-threads=1 --nocapture
```
- `monolithic_relation_audit_is_balanced_and_fully_linked` must stay **balanced AND fully linked** (no dead links). Adding constraints/relations changes the relation count asserted in `proof/tests.rs` — update it (currently 31).
- The distinct-branch / small-u / doubling proofs all exercise mixed-adds AND doublings — they MUST stay green (completeness). A green `assert_constraints` but failing monolithic `prove` = gotcha #1 (degree).

---

## Key files

- `components/fake_glv/ec_source/{air.rs, double_formula.rs, mixed_add_formula.rs, mod.rs}` — the ladder source consumer + the formula modules to REUSE.
- `components/fake_glv/prepared_table/{air.rs, trace.rs}` — **Task A target** (the prepared-table source consumer).
- `components/projective_rcb_mul/{air.rs, trace.rs, relation.rs, tests.rs}` — the silo (15 muls/op), the `ProjectiveRcbMulResultRelation`, the C1 recording-test pattern.
- `field/solinas/air.rs` — C1 fix + the Solinas reduction.
- `curve/projective.rs` — `rcb_double` (:242), `rcb_mixed_add` (:285), `ProjectiveEcRow`. (Source of truth for transcriptions.)
- `proof/mod.rs` — the monolithic proof: `relation_balances()`, `liveness_witnesses()`, `prove_current_air_monolithic`, the PCS/degree config (`p256_stark_monolithic_profile_config`).
- `proof/tests.rs` — the monolithic proof + forgery tests + relation-count assert.

## Suggested order
Task A first (closes the actual remaining hole), with its own soundness review; then Task B (lock in regression coverage for the Double + MixedAdd + prepared-table bindings). After both: full C5 is closed (C2 remains, separately).
