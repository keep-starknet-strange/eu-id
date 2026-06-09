# Close C5: Constrain the Fake-GLV EC Ladder Arithmetic In-AIR

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make verifier acceptance of `verify_current_air_monolithic` actually prove `R = u1·G + u2·Q` by binding every fake-GLV EC ladder operation to constrained projective EC arithmetic in-AIR, closing soundness hole **C5** (and its prerequisite **C1**).

**Architecture:** The `ProjectiveRcbAir` engine (`components/projective_rcb_mul/`) already proves the field multiplications for *every* projective EC operation in the proof — including all ~1000 ladder mults — but it is a **disconnected silo**: it constrains mults only (never `output_point = rcb_op(input_points)`), and its rows are tied to the EC point data the ladder consumes only by the **native** `verify_against_projective_trace` (not an AIR constraint). We complete the architecture that was clearly scaffolded for this: (1) lift the per-row native check into in-AIR coordinate constraints on the silo so it proves the full projective EC op, (2) provide the silo's proven `(op, lhs, rhs, output)` point tuples into a new LogUp relation that the fake-GLV and prepared-table projective sources consume, and (3) fix C1 (the free Solinas correction digit) so the silo's mults are themselves sound. Because the silo's mults are already in the proof, the added proving cost is near-zero (point columns + linear coordinate constraints + one LogUp column), not ~1000 new mults.

**Tech Stack:** Rust, `stwo` (M31 / SIMD backend), the existing `stwo-p256` AIR (`FrameworkEval` constraints + LogUp `relation!` channels + `relation_balances()`), release-mode focused tests via `rtk proxy cargo test`.

---

## Design Decision (read before executing)

Two ways to constrain the ladder's EC arithmetic in-AIR:

- **Option A — re-derive locally in the fake-GLV component** (mirror `final_add`: call `add_projective_rcb_mul_row` for each mult + coordinate reductions, inside `components/fake_glv/ec_source/`). Rejected: it **duplicates ~1000 field mults** that the silo already proves, roughly doubling the projective mul cost of the whole proof, and triplicates the RCB formula logic (final_add, public_key_curve, ladder).

- **Option B (CHOSEN) — revive + link the silo.** The silo already carries and proves the ladder's mults. Add the coordinate constraints there (once), expose its proven point tuples, and have the sources consume them. Near-zero new proving cost; single source of EC-arithmetic truth; closes C5 for the ladder **and** the prepared-table source simultaneously.

> **If the maintainer prefers Option A, the Phase 2–4 task structure changes substantially — flag it before execution.** This plan implements Option B.

**Scope note:** C1 (Phase 1) is a separable, independently valuable fix (it also hardens `final_add`/`public_key_curve`, which use the same Solinas builder). It is included here because the silo's mults must be sound for C5 closure to mean anything. C2 (the scalar-mod-mul AB top digit) is **out of scope** for this plan — it is a separate hole tracked elsewhere.

---

## Current State To Preserve

- The monolithic proof boundary, public-input binding, Fiat-Shamir order, and `relation_balances()` / `liveness_witnesses()` audit machinery in `crates/stwo-p256/src/proof/mod.rs`.
- `final_add` and `public_key_curve` already constrain their EC arithmetic correctly in-AIR via local `add_projective_rcb_mul_row` + coordinate reductions — **do not touch their constraint logic**; they will benefit from the C1 fix automatically.
- `ProjectiveEcTraceClaim::from_native_traces` and `ProjectiveRcbAirTraceClaim::from_projective_trace` (proof/mod.rs:225–230,343–348): the witness-time derivation chain stays; we are adding AIR constraints + a LogUp link, not changing witness generation.
- The native `verify_against_projective_trace` (`components/projective_rcb_mul/trace.rs:245`) stays as a **witness-time sanity check** (completeness), but it must no longer be the *only* thing binding points to mults.

## File Structure

- `crates/stwo-p256/src/field/solinas/air.rs` — **C1 fix**: `add_fp_solinas_reduction_digit` (def ~line 84) range-checks `correction_product_digit` (the free witness, used at air.rs:117, comment at air.rs:37).
- `crates/stwo-p256/src/components/projective_rcb_mul/air.rs` — **Phase 2**: add projective point columns (`lhs/rhs/output` as `x,y,z` limbs) to the silo row, add the RCB coordinate-combination constraints binding them to the existing mul-result columns; **Phase 3**: provide `(op, sig_id, cert_id, lhs, rhs, output)` into the new relation.
- `crates/stwo-p256/src/components/projective_rcb_mul/relation.rs` — **Phase 3**: define `ProjectiveEcOpRelation`.
- `crates/stwo-p256/src/components/fake_glv/ec_source/air.rs` — **Phase 3**: the `FakeGlvProjectiveSourceEval` consumer constrains/links its point columns to the new relation (consume `+active`); remove the vacuous `FakeGlvPrimitiveEcRowRelation` self-loop or repurpose it.
- `crates/stwo-p256/src/components/fake_glv/prepared_table/air.rs` — **Phase 3**: the prepared-table projective source consumes the same relation.
- `crates/stwo-p256/src/proof/mod.rs` — **Phase 4**: add the relation's provider/consumer claimed sums to `relation_balances()` and a nonzero entry to `liveness_witnesses()`.
- `crates/stwo-p256/src/proof/tests.rs` — **Phase 1 & 5**: C1 unit reject test; C5 adversarial forgery tests.
- `crates/stwo-p256/src/components/projective_rcb_mul/tests.rs` — **Phase 2**: silo coordinate-constraint unit tests.

---

## Phase 1: Close C1 — Bind the Solinas Correction Product Digit to Range-Checked 13-bit Digits

**Why first:** the silo's mults (which C5 will rely on) are forgeable until the correction digit is bounded. The fix also hardens `final_add`/`public_key_curve`.

> **CORRECTED 2026-06-09 (original mechanism was infeasible).** The first draft prescribed offsetting `correction_product_digit` by `MAX` and range-checking `2·MAX` via the signed table. That is impossible: `MAX = FP_SOLINAS_CORRECTION_PRODUCT_MAX_ABS_DIGIT = 9·(2¹³−1)² ≈ 2³⁰`, so `2·MAX` exceeds the `MAX_LOG_SIZE = 30` table cap, and the signed table materializes one row per value (~1.2 B rows). **Correct approach:** `correction_product_digit[d]` is *natively* the convolution `sign · Σ_{i+j=d} correction_digit[i]·modulus_limb[j]` (`correction_product_digits`, air.rs:349-362), where `correction_digit[i] ∈ [0,8192)` are the nine 13-bit digits of `|correction|` (`signed_correction_digits`, air.rs:363-378), `modulus_limb[j]` are constant P256 modulus limbs, and `sign∈{−1,+1}`. So commit the **13-bit** digits (Range13 — exact fit) + a sign bit, range-check each digit, and pin `correction_product_digit` to the constrained convolution. Bounded ≤ MAX by construction; no new range table.

**Files:**
- Modify: `crates/stwo-p256/src/field/solinas/air.rs`
- Test: `crates/stwo-p256/src/components/projective_rcb_mul/tests.rs`

- [ ] **Step 1: Read the current reduction-digit constraint to extract exact names.**

Read `crates/stwo-p256/src/field/solinas/air.rs:30-130`. Confirm: (a) the recurrence at air.rs:116-121 `folded_digit - correction_product_digit - result_limb + prev_carry - 2^LIMB_BITS·carry == 0`; (b) `correction_product_digit` has NO `add_range_check` (comment at air.rs:37 admits it "must be supplied by the correction-product accumulator relation" — which does not exist); (c) the host-only bound `FP_SOLINAS_CORRECTION_PRODUCT_MAX_ABS_DIGIT` (`FpSolinasReductionRow::verify`, air.rs:246) — this is the magnitude the AIR must enforce.

- [ ] **Step 2: Write a failing soundness unit test.**

In `crates/stwo-p256/src/components/projective_rcb_mul/tests.rs`, add a test that builds a one-row projective mul trace, then mutates `correction_product_digit` of one reduction digit to an out-of-range value that still satisfies the linear recurrence (compensate by adjusting `result_limb`/`carry`), and asserts `assert_constraints` (or the component's PCS path) now **fails**. Use the existing `one_row_trace` helper (tests.rs) and the existing constraint-assertion helper in that file as the template.

```rust
#[test]
fn solinas_reduction_rejects_out_of_range_correction_digit() {
    // Build a valid one-row RCB mul trace, then forge a correction digit
    // outside [-MAX_ABS, MAX_ABS] while keeping the line-117 recurrence
    // satisfiable (shift result_limb/carry). Pre-fix: constraints PASS (bug).
    // Post-fix: the new range check makes constraints FAIL.
    let mut base = /* gen base trace for one_row_trace(ProjectiveEcOp::MixedAdd, ..) */;
    forge_correction_digit_out_of_range(&mut base, /*digit=*/0);
    assert_projective_rcb_constraints_fail(&base); // helper: expects Err
}
```

- [ ] **Step 3: Run it; verify it FAILS to fail (i.e. currently passes → bug confirmed).**

Run: `rtk proxy cargo test -p stwo-p256 solinas_reduction_rejects_forged_correction_product_digit --release -- --test-threads=1 --nocapture`
Expected (pre-fix): test FAILS because the forged proof still satisfies constraints (demonstrates C1).

- [ ] **Step 4: Add the range check in `add_fp_solinas_reduction_digit`.**

In `crates/stwo-p256/src/field/solinas/air.rs`, inside `add_fp_solinas_reduction_digit` (alongside the existing `add_range_check` calls for `folded_digit`/`result_limb`/`prev_carry`/`carry`), add a range check that bounds `correction_product_digit` to its signed magnitude `FP_SOLINAS_CORRECTION_PRODUCT_MAX_ABS_DIGIT`. The digit is signed, so use the existing signed-range pattern (the same approach used for `prev_carry`/`carry` signed range checks in this function — read them and replicate, offsetting by `MAX_ABS` to map to a non-negative range, then range-checking the offset value to `2·MAX_ABS`). Wire the range relation through the existing relation parameter the function already receives.

> The exact `add_range_check`/`add_signed_range_check` call must be transcribed from the sibling carry checks in this same function (they already range-check signed quantities) — do not invent a new range mechanism.

- [ ] **Step 5: Run the new test (now passes) + the existing solinas/projective suite (no regressions).**

Run:
```
rtk proxy cargo test -p stwo-p256 solinas_reduction_rejects_forged_correction_product_digit --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 projective_rcb --release -- --test-threads=1 --nocapture
```
Expected: new test PASS; existing projective/solinas tests PASS. The new range check consumes an existing range table (range13/raw_product_carry16) — confirm the consumed range relation is balanced in `relation_balances()` (the range provider's claimed sum must absorb the new consumer terms).

- [ ] **Step 6: Update stale relation/range-count test expectations.**

The recent commit history shows width/count tests assert exact range-check counts (e.g. `024f389 bump stale relation-audit count`). Adding a per-digit range check changes those counts. Run the width/shape diagnostics and update the asserted constants to the new measured values:
```
rtk proxy cargo test -p stwo-p256 width --release -- --test-threads=1 --nocapture
```

- [ ] **Step 7: Commit.**

```bash
rtk git add crates/stwo-p256/src/field/solinas/air.rs crates/stwo-p256/src/components/projective_rcb_mul/tests.rs
rtk git commit -m "fix(p256): range-check Solinas correction digit (close C1 free-witness forgery)"
```

---

## C5 BUILD — B2 DESIGN (APPROVED 2026-06-09; supersedes the B1 Phase 2–3 below)

Investigation findings that reshape the build:
- **Mul count is 13 per op** (`PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP = 13`; 13 Double + 13 MixedAdd slots in the `ProjectiveRcbMulStep` enum, trace.rs:1991), NOT 6/11.
- The silo commits **one mul per row** (`lhs`,`rhs`,`result` + reduction + the new C1 correction digits), **no point columns**. The `fp_add`/`fp_sub` glue tying mul results into `x3,y3,z3` is native Rust.
- The `output = rcb_op(inputs)` binding currently exists **only** as a native recompute-and-compare (`verify_against_projective_row` → `from_projective_row`, trace.rs:1306-1344). That is the C5 hole.
- `ProjectiveEcRow` (curve/projective.rs:78): inputs **affine** (`lhs_affine`,`rhs_affine`), output dual (`output_affine` + `output_projective{x,y,z}`). Affine↔projective conversion is native (`to_prepared` z-inversion).
- Precedent to mirror: `final_add` — `FinalAddMulEval` PROVIDES mul limbs via `FinalAddMulResultRelation`; `FinalAddCheckEval` CONSUMES specific muls + constrains the coordinate formula via `add_*_reduction` helpers (final_add/air.rs:64,321,413-456).

**B2 = mirror final_add:** the silo PROVIDES its proven mul-results into a new relation; the existing affine source-consumer (already per-EC-op, already commits the points) CONSUMES them and constrains the coordinate formula. No new silo columns; reuses the consumer's points + final_add's reduction idiom.

### Task C5-1: Establish the balanced silo→source mul-result link (plumbing, no formula yet)
Files: `projective_rcb_mul/{relation,air,interaction}.rs`, `fake_glv/ec_source/air.rs`, `fake_glv/prepared_table/air.rs`, `proof/mod.rs`.
- Define `relation!(ProjectiveRcbMulResultRelation, 5)` keyed `(source_index, mul_index, role, limb_index, limb)`; role ∈ {LHS=0,RHS=1,RESULT=2} (constants `PROJECTIVE_RCB_MUL_ROLE_*` exist). Add to `ProjectiveRcbMulComponentRelations` (+draw/dummy/as_refs).
- Silo `ProjectiveRcbMulEval::evaluate`: after the mul constraints, PROVIDE each role×limb with `+active` (mirror `provide_mul_limbs`). No new silo columns.
- Source consumers (`FakeGlvProjectiveSourceEval` + prepared-table source): commit the mul-result limb columns they will need and CONSUME them with `-active` keyed by `(source_index, mul_index, role, limb)`. **No coordinate constraints yet** — just balance the link.
- Wire `relation_balances()` (`("ProjectiveRcbMulResult", provider + consumers)`) and `liveness_witnesses()` (`("ProjectiveRcbMulResult", silo_provider_sum)`).
- Verify: monolithic proof still proves+verifies; `monolithic_relation_audit_is_balanced_and_fully_linked` balanced AND the new link live. NO soundness change yet (consumer reads muls but doesn't constrain the formula).

### Task C5-2: Constrain the coordinate formula in the source consumer (THE SOUNDNESS CORE — air-writer review REQUIRED)
Files: `fake_glv/ec_source/air.rs` (+ prepared-table source); reuse `final_add` `add_*_reduction` helpers (degree ≤2).
- **Step 1 — transcribe** the exact 13-slot formula for Double and MixedAdd from `curve/projective.rs:242` / `:285` + the `ProjectiveRcbMulStep` slot map (trace.rs:1991): the ordered (operand_a, operand_b)→result of the 13 muls and the `fp_add`/`fp_sub` glue producing the working values and `x3,y3,z3`. Record it.
- **Step 2 — columns:** add committed projective working-value columns + per-coordinate quotient/carry columns in the consumer. Affine inputs ⇒ `z1 = 1` (constant); infinity via the `inf` flag.
- **Step 3 — constrain** (branch-selected by `op`, reusing the limb-reduction idiom):
  (a) **Operand binding** — each consumed mul's `lhs`/`rhs` limbs equal the correct linear combo of input coords / prior results (NOT just the `result`, else a wrong-operand forgery survives). This is the bulk and the soundness-critical part.
  (b) **Output projective** — `x3,y3,z3` equal the final linear combos of mul results.
  (c) **Affine normalization** — `output_affine.x · z3 ≡ output_projective.x` and `output_affine.y · z3 ≡ output_projective.y` (binds the committed affine output to the projective result; degree-2). Do NOT leave the affine output bound only natively.
  (d) **Infinity / inactive** — gate the finite branch; `inf` rows force `output = other input`; inactive ⇒ zero.
- Verify: a forged ladder `output` point is now rejected by `assert_constraints`; valid proofs still prove+verify; relation audit still balanced+live.

### Task C5-3: Adversarial forgery tests (was Phase 5)
- Forge a ladder `output` point in the proof claim → `verify_current_air_monolithic` rejects. Same for an intermediate Double output and a prepared-table multiple. Confirm pre-C5-2 these verified (the contrast proves closure).

**Risks:** operand-binding (a) is the subtle soundness point; affine-normalization (c) must bind the committed affine output; mul-limb consumption may add more columns than the first cost estimate (commit only what the formula needs); air-writer review of the 13-slot transcription before merge. Projective→affine downstream: confirm the ladder result reaches final_check only via `final_add` (affine output) so no new normalization gadget is needed.

---

## Phase 2 (B1 — SUPERSEDED by B2 above): Make the Silo Constrain the Full Projective EC Operation

Lift the native per-row check (`verify_against_projective_row`) into in-AIR constraints: the silo must prove `output_point = rcb_double(lhs)` (op=1) or `output_point = rcb_mixed_add(lhs, rhs)` (op=0), using its **existing** mul-result columns.

**Files:**
- Modify: `crates/stwo-p256/src/components/projective_rcb_mul/air.rs`
- Modify: `crates/stwo-p256/src/components/projective_rcb_mul/trace.rs` (add point columns to the base trace)
- Test: `crates/stwo-p256/src/components/projective_rcb_mul/tests.rs`

- [ ] **Step 1: Transcribe the exact RCB formula + mul ordering.**

Read `crates/stwo-p256/src/curve/projective.rs:242-282` (`rcb_double`, 6 `fp_mul`) and `:285-353` (`rcb_mixed_add`, 11 `fp_mul`). Write down, for each op, the ordered list of mults `(operand_a, operand_b) → product` and the coordinate equations producing `x3,y3,z3` from those products via `fp_add`/`fp_sub`/scalar-by-`b`. Read `crates/stwo-p256/src/components/final_add/air.rs:413-456` (`add_sub_reduction`, `add_slope_numer_reduction`, `add_x3_reduction`) as the **idiom template** for expressing "`coord = Σ products/coords − q·p`" as an in-AIR limb reduction with a quotient/carry. This step produces the concrete constraint list used in Step 4 — record it in the task notes.

- [ ] **Step 2: Add projective point columns to the silo base trace.**

In `trace.rs`, extend the silo row's base-trace generation to emit `lhs = (x,y,z)`, `rhs = (x,y,z)`, `output = (x3,y3,z3)` limbs (`N_LIMBS` each) from the `ProjectiveEcRow` it already holds, plus the `op` code. (The data is already present in `ProjectiveEcRow`; this only widens the committed columns.) Update the column-count constant for the silo base trace and any `assert_eq!(column, ...)` in the row-packing fn.

- [ ] **Step 3: Write a failing test: forged output point passes the silo.**

In `tests.rs`, build a valid one-row mul trace for `MixedAdd`, then mutate one limb of the `output` point columns (a forged R) **without** changing the mul-result columns, and assert the silo constraints FAIL.

```rust
#[test]
fn silo_rejects_output_point_inconsistent_with_muls() {
    let mut base = /* gen silo base trace, one MixedAdd row */;
    forge_output_x_limb(&mut base, /*limb=*/0);
    assert_projective_rcb_constraints_fail(&base); // pre-Step-4: PASSES (no coord constraint) → test fails
}
```

- [ ] **Step 4: Run it (confirms the gap), then add the coordinate constraints.**

Run: `rtk proxy cargo test -p stwo-p256 silo_rejects_output_point_inconsistent_with_muls --release -- --test-threads=1 --nocapture` → expected pre-fix FAIL (forgery accepted).

In `air.rs`, inside the silo's `evaluate`, after reading the existing mul-result columns and the new point columns, add the coordinate-combination constraints from Step 1, **branch-selected by `op`**:
- `op` boolean (`op·(op−1)=0`).
- doubling branch gated by `op`, mixed-add branch gated by `(1−op)`.
- For each branch, the `x3/y3/z3` reductions binding output limbs to the mul products + input coords (transcribed from Step 1, using the `add_*_reduction` idiom from `final_add/air.rs:413-456`).
- Point well-formedness: reuse the existing `inf`/zeroing pattern from `PreparedTableEcEvalPoint::add_constraints` (`prepared_table/air.rs:459`) so infinity/padding rows are handled.

Constraint degree budget: keep each reduction degree ≤ `log_size + 1` (the silo's `max_constraint_log_degree_bound`). Products are already materialized columns, so coordinate equations are linear in committed values — degree stays low.

- [ ] **Step 5: Run the test (now passes) + full silo suite.**

```
rtk proxy cargo test -p stwo-p256 silo_rejects_output_point_inconsistent_with_muls --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 projective_rcb --release -- --test-threads=1 --nocapture
```
Expected: forgery now rejected; existing silo tests pass.

- [ ] **Step 6: Commit.**

```bash
rtk git add crates/stwo-p256/src/components/projective_rcb_mul/air.rs crates/stwo-p256/src/components/projective_rcb_mul/trace.rs crates/stwo-p256/src/components/projective_rcb_mul/tests.rs
rtk git commit -m "feat(p256): constrain projective EC point formula in-AIR in RCB silo"
```

---

## Phase 3: Link the Silo to the Projective Sources via LogUp

Now the silo proves `output = rcb_op(inputs)`. Expose those tuples and make the fake-GLV ladder + prepared-table sources consume them, so the ladder's claimed points are forced to equal silo-proven points.

**Files:**
- Modify: `crates/stwo-p256/src/components/projective_rcb_mul/relation.rs`
- Modify: `crates/stwo-p256/src/components/projective_rcb_mul/air.rs`
- Modify: `crates/stwo-p256/src/components/fake_glv/ec_source/air.rs`
- Modify: `crates/stwo-p256/src/components/fake_glv/prepared_table/air.rs`

- [ ] **Step 1: Define the EC-op relation.**

In `relation.rs`, add (arity = the point-tuple width: `op` + `sig_id` + `cert_id` + 3 points × `PREPARED_TABLE_EC_POINT_COLUMNS`; compute exactly and name the const):

```rust
relation!(ProjectiveEcOpRelation, PROJECTIVE_EC_OP_RELATION_ARITY);
```

Add `pub projective_ec_op: ProjectiveEcOpRelation` to `ProjectiveRcbMulComponentRelations` (relation.rs:45) and its `draw`/`dummy`/`as_refs` (relation.rs:58,84).

- [ ] **Step 2: Provider — silo yields its proven tuples.**

In the silo `evaluate` (`projective_rcb_mul/air.rs`), after the Phase-2 coordinate constraints, emit `add_to_relation(RelationEntry::new(&relations.projective_ec_op, -active, &tuple))` where `tuple = [op, sig_id, cert_id, lhs.x.., lhs.y.., lhs.inf, rhs.., output..]`. Expose a `provider_claimed_sum` on the silo's interaction claim (mirror an existing provider sum in this component).

- [ ] **Step 3: Consumer — fake-GLV projective source consumes.**

In `components/fake_glv/ec_source/air.rs`, change `FakeGlvProjectiveSourceEval::evaluate` (currently emits the vacuous `FakeGlvPrimitiveEcRowRelation` at air.rs:298) to instead consume the new relation: `add_to_relation(RelationEntry::new(&relations.projective_ec_op, +active, &same_tuple_shape))`. The ladder-side provider (`FakeGlvPrimitiveEcRowProviderEval`, air.rs:241) keeps emitting the ladder rows; the ladder↔source identity is what forces ladder points = silo-proven points. (Decide: either keep `FakeGlvPrimitiveEcRowRelation` for ladder↔source and add `ProjectiveEcOpRelation` for source↔silo, or collapse into one. Keeping both is lower-risk and makes the audit explicit.)

- [ ] **Step 4: Consumer — prepared-table projective source consumes.**

In `components/fake_glv/prepared_table/air.rs`, make the prepared-table projective-source eval consume `ProjectiveEcOpRelation` (`+active`) the same way, closing the prepared-table point-generation hole with the same mechanism.

- [ ] **Step 5: Generate the interaction (LogUp) traces for the new relation.**

In each component's interaction-trace generator, add a column for `ProjectiveEcOpRelation` (provider in the silo gen fn; consumer in the two source gen fns), following the existing `fake_glv_primitive_ec_row` interaction-gen pattern (`ec_source/air.rs:390-415`). Each side returns its `claimed_sum`.

- [ ] **Step 6: Build (no balance wiring yet) to shake out arity/column mismatches.**

Run: `rtk proxy cargo build -p stwo-p256 --release` → fix any tuple-arity / column-count mismatches. Do not run proofs yet (the balance is intentionally unwired until Phase 4).

- [ ] **Step 7: Commit.**

```bash
rtk git add crates/stwo-p256/src/components/projective_rcb_mul crates/stwo-p256/src/components/fake_glv
rtk git commit -m "feat(p256): add ProjectiveEcOpRelation linking RCB silo to fake-glv/prepared-table sources"
```

---

## Phase 4: Wire the Balance + Liveness Audit

**Files:**
- Modify: `crates/stwo-p256/src/proof/mod.rs`
- Modify: `crates/stwo-p256/src/proof/balances.rs`

- [ ] **Step 1: Add the balance entry.**

In `relation_balances()` (`proof/mod.rs`, the `vec![...]` around line 800), add:

```rust
(
    "ProjectiveEcOp",
    self.projective_rcb_air.projective_ec_op_provider_claimed_sum
        + self.fake_glv_projective_source.projective_ec_op_consumer_claimed_sum
        + self.prepared_table_projective_source.projective_ec_op_consumer_claimed_sum,
),
```

(Thread the new `*_claimed_sum` fields through the interaction-claim structs; mirror an existing 3-term balance such as `ScalarSetupRange13` at proof/mod.rs:829.)

- [ ] **Step 2: Add the liveness witness.**

In `liveness_witnesses()` (`proof/mod.rs:932`), push:

```rust
("ProjectiveEcOp", self.projective_rcb_air.projective_ec_op_provider_claimed_sum),
```

so a zero (silo never linked to a source → forgery surface re-opened) makes `dead_links()` (mod.rs:1023) non-empty and fails the audit test.

- [ ] **Step 3: Run the relation-audit test.**

Run: `rtk proxy cargo test -p stwo-p256 monolithic_relation_audit_is_balanced_and_fully_linked --release -- --test-threads=1 --nocapture`
Expected: PASS — balanced AND no dead links (the new link is live).

- [ ] **Step 4: Run the primary monolithic proof gates (completeness regression).**

```
rtk proxy cargo test -p stwo-p256 current_p256_proof_pipeline_proves_and_verifies_current_air_monolithic_proof --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 current_p256_proof_pipeline_proves_and_verifies_monolithic_distinct_branch --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 current_p256_monolithic_proves_arbitrary_doubling_final_add --release -- --test-threads=1 --nocapture
```
Expected: all PASS — valid signatures still prove and verify (we added constraints satisfied by honest witnesses).

- [ ] **Step 5: Commit.**

```bash
rtk git add crates/stwo-p256/src/proof/mod.rs crates/stwo-p256/src/proof/balances.rs
rtk git commit -m "feat(p256): balance + liveness-audit the ProjectiveEcOp link (close C5)"
```

---

## Phase 5: Adversarial Forgery Tests (Definition of Done)

C5 is closed only when forging the ladder output is rejected by the **verifier**, not just by native checks.

**Files:**
- Modify: `crates/stwo-p256/src/proof/tests.rs`

- [ ] **Step 1: Forge a ladder output point in the proof claim.**

Add a test that builds a valid monolithic proof, then mutates one limb of a fake-GLV ladder `output` point (the R-bearing row) in the proof/interaction claim — exactly like the existing `monolithic_rejects_mutated_*` tests mutate other claim fields — and asserts `verify_current_air_monolithic` returns `Err`.

```rust
#[test]
fn current_p256_monolithic_rejects_forged_ladder_output_point() {
    let input = valid_real_input_with_small_u_scalars();
    let proof = P256ProofDraft::from_inputs(vec![input]).expect("draft")
        .prove_current_air_monolithic::<Blake2sMerkleChannel>().expect("prove");
    let mut forged = proof.clone();
    forge_fake_glv_ladder_output_limb(&mut forged, /*row=*/LAST_ADD_ROW, /*limb=*/0);
    assert!(verify_current_air_monolithic::<Blake2sMerkleChannel>(forged).is_err(),
        "C5: forged ladder output point must be rejected by the verifier");
}
```

- [ ] **Step 2: Run it.**

Run: `rtk proxy cargo test -p stwo-p256 current_p256_monolithic_rejects_forged_ladder_output_point --release -- --test-threads=1 --nocapture`
Expected: PASS (forgery rejected). Before Phases 2–4 this mutation verified successfully — that contrast is the proof that C5 is closed.

- [ ] **Step 3: Add the same for a prepared-table point and an intermediate doubling row.**

Two more tests: forge a prepared-table multiple, and forge an intermediate `Double` row output. Both must be rejected.

- [ ] **Step 4: Run the full mutation suite (no regressions in other rejections).**

Run: `rtk proxy cargo test -p stwo-p256 monolithic_rejects --release -- --test-threads=1 --nocapture`
Expected: all existing + new rejection tests PASS.

- [ ] **Step 5: Commit.**

```bash
rtk git add crates/stwo-p256/src/proof/tests.rs
rtk git commit -m "test(p256): adversarial ladder/prepared-table point forgery rejection (C5 closed)"
```

---

## Final Acceptance Gate

Run one at a time in release mode:

```bash
rtk proxy cargo test -p stwo-p256 solinas_reduction_rejects_forged_correction_product_digit --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 silo_rejects_output_point_inconsistent_with_muls --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 monolithic_relation_audit_is_balanced_and_fully_linked --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 current_p256_monolithic_rejects_forged_ladder_output_point --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 monolithic_rejects --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 current_p256_proof_pipeline_proves_and_verifies_current_air_monolithic_proof --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 current_p256_air_shape_diagnostic --release -- --ignored --test-threads=1 --nocapture
```

Acceptance criteria:

- Forging any ladder output point, intermediate doubling output, or prepared-table multiple is **rejected by `verify_current_air_monolithic`** (Phase 5).
- The Solinas correction digit is range-checked; an out-of-range digit is rejected (Phase 1).
- The silo constrains `output_point = rcb_op(input_points)` in-AIR; a point inconsistent with its mults is rejected (Phase 2).
- `ProjectiveEcOp` link is balanced **and live** (`dead_links()` empty) — the ladder cannot silently detach from the silo (Phase 4).
- All previously-green valid-signature proofs still prove and verify (no completeness regression).
- `current_p256_air_shape_diagnostic` confirms proving cost did not balloon (the mults already existed; only point columns + coordinate constraints + 1 LogUp column added).

---

## Risks & Notes

- **C5 ≠ sound P-256 verifier alone.** After this plan, C2 (scalar-mod-mul AB top digit, `s·u1`/`s·u2` reductions forgeable) is still open, and the selector still pins the trivial scalar slice (completeness). Closing C5+C1 makes the *EC arithmetic* sound; the full arbitrary-signature verifier also needs C2 + the selector generalization (see [the completeness plan](2026-06-05-arbitrary-p256-signature-air.md)).
- **Coordinate-constraint correctness is the soundness-critical step (Phase 2 Step 4).** It must be transcribed exactly from the native `rcb_double`/`rcb_mixed_add` formulas — a wrong reduction would either reject valid inputs (caught by Phase 4 Step 4) or, worse, admit a forgery (caught by Phase 5). Have the `air-writer` skill review the Phase 2 constraints before merging.
- **Projective vs affine output.** The silo proves projective `(x3,y3,z3)`; downstream consumers (final_check) need affine `x(R)`. Confirm the existing affine-conversion / `FinalAddOutputRelation` path already normalizes the ladder result — if the ladder result reaches final_check only via final_add (which outputs affine `x3`), no new normalization constraint is needed here.
- **Liveness for multi-signature.** If a proof can carry zero active ladder rows (degenerate), ensure the liveness witness is only required nonzero when there is an active certificate (mirror how existing liveness entries handle the inactive case).
```