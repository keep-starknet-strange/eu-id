# P-256 STWO AIR — Soundness / Safety / Optimization Audit

**Date:** 2026-06-08
**Scope:** the whole `crates/stwo-p256` AIR (≈47k LoC) — the live monolithic proof path
`prove_current_air_monolithic` / `verify_current_air_monolithic` and every component it
instantiates, plus dormant scaffolding.
**Method:** the `air-writer` soundness methodology (four invariants: witness uniqueness,
logup balance, domain/range enforcement, public-input binding) applied per-subsystem by
parallel auditors, cross-checked against the implementation spec
(`docs/p256_fake_glv_air_full_spec.md`), with the headline findings re-verified by hand.
**Pass 2 (2026-06-08):** an independent re-derivation from current source (line level), which
confirmed C1/C2 first-hand and **elevated the EC-ladder gap to a third confirmed live forgery
(C5)** — see the "Pass 2" section below.

**POST-REORG PATH NOTE (2026-06-08):** after this audit, `crates/stwo-p256` was reorganized
(behavior-identical — every finding below is unchanged) into `field/ curve/ gadgets/ components/
proof/`. The `file:line` references below are PRE-reorg. New locations: `fp_solinas_air.rs`→
`field/solinas/air.rs`; `projective_air.rs`→`components/projective_rcb_mul/{air,trace,interaction,
relation}.rs`; `scalar_mod_mul/*`→`components/scalar_mod_mul/*`; `fake_glv_scalar.rs`→
`components/fake_glv/scalar/air.rs`; `fake_glv_ec_source.rs`→`components/fake_glv/ec_source/air.rs`;
`fake_glv_selector*.rs`→`components/fake_glv/selector/*`; `fake_glv_chain*.rs`→
`components/fake_glv/chain/*`; `prepared_table.rs`→`components/fake_glv/prepared_table/*`;
`final_add_air.rs`→`components/final_add/*`; `final_check_air.rs`→`components/final_check/*`;
`public_key_curve_air.rs`→`components/public_key_curve/*`; `proof.rs`→`proof/{mod,balances,tests}.rs`;
`ecdsa.rs`→`reference/ecdsa.rs`. Line numbers also shifted (deletions + splits).

---

## Verdict

**The live AIR is NOT sound today: a malicious prover can produce accepting proofs of false
ECDSA statements.** There are at least **three** *independently confirmed, live-path* forgeries:
C1 (every Fp multiply), C2 (the `s·u1`/`s·u2` reductions), and **C5 (the elliptic-curve
scalar-multiplication ladder itself is unconstrained)**. Any one alone forges an ECDSA acceptance.

The good news: the unsoundness is **concentrated in known-incomplete wiring** — free-witness
placeholders where a binding relation was planned but not yet built, and constraints explicitly
toggled off. These are *missing* constraints, not *wrong* ones. The surrounding architecture
(relation-balance discipline, native EC formulas, range-check design, public-input binding,
Fiat-Shamir order) is sound and in several places unusually careful. This matches the README's
"not audited, not production-ready, end-to-end API intentionally not exposed" status.

Separately, the fake-GLV machinery is **split across two stages**: the **scalar-equation layer is
general and live** (`fake_glv_scalar.rs:248` calls `constrain_fake_glv_scalar_general`, enforcing
`S·s2_abs + (1−2·s2_sign_bit)·s1 − q·n = 0` via the live ScalarModMul limb links — commits
`b337098`/`a60e1bf`/`75ebbcb`; the proof.rs:300-306 "enforces the trivial constraints" comment is
**stale** for this layer). But the **selector/windowing reconstruction is still trivial**
(`fake_glv_selector.rs:192` calls `constrain_selector_from_trivial_scalar`, which pins `s2_abs=1`),
and every live prove/verify test uses `from_inputs_with_trivial_fake_glv_hints` (the arbitrary-hint
e2e is `#[ignore]` "pending selector AIR generalization"). So it is **not yet a working general
P-256 verifier end-to-end** — the remaining trivial piece is the selector/chain (decode bindings,
canonical negation, s2 reconstruction), not the scalar arithmetic.

---

## Pass 2 — independent re-verification (2026-06-08)

A second, independent pass re-derived the headline findings directly from the current source (not
from this document), at line level, and surfaced one finding that pass 1 understated.

**Re-verified first-hand (confirmed, live):**

* **C1** — `add_fp_solinas_reduction_digit` (`fp_solinas_air.rs:84-122`) range-checks `folded_digit`,
  `result_limb`, `prev_carry`, `carry` but **not** `correction_product_digit`;
  `add_projective_rcb_mul_row` (`projective_air.rs:834-931`) binds `folded_digit` / `folded_carry` /
  the carry chain but never `correction_product_digit`. Grep confirms it is bound by no relation or
  range check anywhere in the AIR — only a host-side `.abs() >` check at `fp_solinas_air.rs:246`
  (proving-time completeness, not a constraint) and the free read at `projective_air.rs:825`.
* **C2** — `component.rs:29` `…ENABLE_AB_TOP_DIGIT_CONSTRAINT = false`; `component.rs:613-641`
  range-checks only `digits[0]`/`digits[1]` and gates the `digits[2]` boolean **off for `SIDE_AB`**
  (QN keeps it via `QN_ARITHMETIC=true`); `layout.rs:125-130` confirms only `digits[0]`/`digits[1]`
  enter the Range13 uses. AB `digits[2]` is a free ~2³¹ value, pinned only by `product_sum ≡
  d0 + 2¹³·d1 + 2²⁶·d2 (mod M31)`.
* **Trivial-path degeneracy** — `fake_glv_selector.rs:523` (`constrain_selector_from_trivial_scalar`,
  live at `:192`) pins `s2_abs = 1`, so the only exercised path computes a *degenerate* scalar
  multiplication. `constrain_fake_glv_scalar_general` exists and is live in the *scalar* AIR, but the
  *selector* AIR stays trivial-only — which is why the real-signature e2e is `#[ignore]`'d.

**Cross-checked, consistent (no false positives in the sampled findings):** C3, C4, H1–H6, and the
Range / strengths sections matched the code where sampled. The pass-1 method is sound and its two
headline findings are accurate.

### C5 — the EC scalar-multiplication ladder is unconstrained ⇒ `R = u1·G + u2·Q` is forgeable (most fundamental live hole)
**Files:** `scalar/fake_glv_ec_source.rs:223-265` (provider eval), `:283-322` (source eval);
`scalar/fake_glv_chain_expansion.rs` (step decomposition); negative grep across `scalar/`.
**Newly elevated in pass 2** — pass 1 flagged this only as a soft "worth confirming" note (§5).

The `projective_air.rs` engine proves `result = lhs·rhs (mod p)` and is wired into `final_add_air`
and `public_key_curve_air` — but **never into the fake-GLV scalar-mul ladder.** Grep across `scalar/`
for `rcb_double|rcb_mixed_add|ProjectiveRcbMul|consume_mul|provide_mul` returns **zero hits**: the
ladder never invokes the mod-p multiplication engine or the curve formulas as constraints.

Instead the ladder's per-step EC operations flow through `FakeGlvPrimitiveEcRowRelation`, whose only
two emission sites are both in `fake_glv_ec_source.rs`:

* `FakeGlvPrimitiveEcRowProviderEval` (`:223-265`): reads `(active, source_index, sig_id, cert_id,
  op, lhs, rhs, output)` as free trace masks; constrains only `active∈{0,1}`, `op∈{0,1}`, the
  `source_index` linkage, per-point well-formedness, and inactive⇒zero; yields the tuple with
  **−active**.
* `FakeGlvProjectiveSourceEval` (`:283-322`): reads the same shape and yields it with **+active**.

There is **no constraint anywhere that `output == rcb_double(lhs)` or `output ==
rcb_mixed_add(lhs, rhs)`.** `chain_expansion` faithfully *decomposes* each ladder step into
`double → double → mixed_add` and binds the pieces by lookup to these primitive rows — but because the
primitive rows carry no formula, a matching row exists for *any* `(lhs, output)` the prover writes.
The native `rcb_double` / `rcb_mixed_add` (`projective.rs`) are correct Rust enforced only by a
proving-time `if … { Err }` (`projective_air.rs:3282`) — completeness, not soundness. The
`−active/+active` pair is a closed tautological loop that proves only "two trace regions hold the
same point tuples," never that those points satisfy the group law.

*Exploit:* witness the per-step primitive EC rows with any point sequence that makes the
continuity / expansion lookups balance and lands the accumulator on a chosen `R` (and the prepared
`DoubleR` hint at `±R`). `final_add_air` / `final_check_air` then honestly process the forged `R`;
the proof verifies although `u1·G + u2·Q` was never computed. **Live on the trivial path** (the only
path exercised) and **independent of C1/C2** — fixing the Fp engine does not touch it, because the
ladder doesn't use the Fp engine.

*Fix (largest of all findings):* bind each ladder step's `output` to `rcb_double` /
`rcb_mixed_add` of its inputs by routing the step's coordinate arithmetic through the
`projective_air` mod-p mul engine (consume `ProjectiveRcbMulLimb`-style tuples), exactly as
`final_add_air` already does for the final addition. This turns `FakeGlvPrimitiveEcRowRelation` into
a real bridge to constrained arithmetic rather than a closed tautology.

---

## Garaga cross-check (`msm_fake_glv`) + applied fix

The fake-GLV scalar layer was compared against the reference Garaga implementation
(`~/garaga`): the Python `hydra/garaga/hints/fake_glv.py`, the Rust port
`tools/garaga_rs/src/hints/fake_glv.rs`, and the in-circuit verifier
`src/src/ec/ec_ops.cairo::_scalar_mul_fake_glv`. P-256 uses Garaga's **pure** fake-GLV (the
non-endomorphism path, `get_fake_glv_hint`) — there is no `φ`/eigenvalue/`third_root_of_unity`.

**Consistent:** our `fake_glv_decompose.rs` faithfully ports `precompute_lattice` (V1 = `(rem, −t)`,
relation `s1 + scalar·s2 ≡ 0 mod n`, 2¹²⁸ bounds), and the spec/AIR verification structure matches
`scalar_mul_fake_glv` (nbits=128, ±{P,3P}±{R,3R} window, `selector = a + 4·b`, MSB init, +3R baked
into the last step, final `Acc == [3]·R_signed`). The sign convention differs cosmetically (Garaga
signs `s2`/`R`; we sign `s1` and negate `H`) but is algebraically equivalent.

**Inconsistent (now being fixed):** Garaga's circuit enforces **`assert(_s2_abs != 0)`**
(`ec_ops.cairo:254`) — the load-bearing check that makes `[s2_abs]` injective, so the chain identity
forces `H = [S]P`. With `s2_abs ≠ 0`, `S ≠ 0`, and the decomposition relation, `s1 = 0` is then
infeasible, so Garaga needs only this one check (not a separate `s1 > 0`). Our live general scalar AIR
enforced **neither** (finding C3). Garaga also bounds `s1, s2_abs < 2¹²⁸` *structurally* via the
`u128` type (`ec_ops.cairo:143,222`); we must range-check, which the trivial selector + Range13-not-Range11
quotient limb under-enforce (finding H3) — that bound lands with the selector generalization.

**Fix applied** (mirrors Garaga's `s2_abs ≠ 0`): `fake_glv_scalar.rs` now witnesses `s2_abs_inv` and
adds the degree-2 nonzero gadget `Σ s2_abs · s2_abs_inv = cert_active` in
`constrain_fake_glv_scalar_general` (the `s2_abs` limbs are 13-bit via the ScalarModMul role-`B` link,
so the sum cannot wrap M31). On the nonzero branch this forces `s2_abs ≠ 0`; it is vacuous on the
zero/padding branches. Preserves the `log_size + 1` degree bound. This closes the C3 forge in the
general path (currently masked anyway by the trivial selector pinning `s2_abs = 1`). The `< 2¹²⁸`
bound (H3 / selector reconstruction) remains for the selector-generalization work.

---

## 1. Confirmed live-path CRITICAL soundness holes (verified by hand)

### C1 — `correction_product_digit` is an unconstrained free witness ⇒ every Fp multiply is forgeable
**Files:** `fp_solinas_air.rs:67,117` (recurrence), `projective_air.rs:825` (free read).
**Independently found by two auditors.**

The Solinas reduction digit enforces
`folded_digit − correction_product_digit − result_limb + prev_carry − 2¹³·carry = 0`.
`folded_digit`, `result_limb`, and the carries are range-checked; `correction_product_digit` is
**not** range-checked and is bound by **no relation anywhere** (grep across
`projective_air`/`public_key_curve_air`/`final_add_air` for a `correction` range/relation:
zero hits). The code comment (lines 37–39) states it "must be supplied by the correction-product
accumulator relation in the full component" — that accumulator was never implemented.

*Exploit:* set `correction_product_digit := folded_digit − result_limb + prev_carry − 2¹³·carry`
per digit; the recurrence holds for **any** 13-bit `result_limb`. So the reduced result is
decoupled from `lhs·rhs mod p`. This breaks every Fp multiplication used by the projective EC
engine and the public-key on-curve check `y² = x³ − 3x + b` ⇒ EC arithmetic and ECDSA acceptance
are forgeable. **Live in production verify.**

*Fix:* build the correction-product accumulator relation — witness the signed correction digits,
range-check them, and bind `correction_product_digit[i]` to `Σ_j sign·corr_digit_j·p_limb`
exactly as `FoldedDigit`/`FoldedContribution` pin the fold. Then re-derive the carry bound (see
H1) and make the headroom asserts pass (H4).

### C2 — AB product-chunk `digits[2]` is unconstrained ⇒ `s·u1`, `s·u2` reductions forgeable
**Files:** `scalar/scalar_mod_mul/component.rs:29,614-618,629-639`, `layout.rs:126,129`.

`SCALAR_MOD_MUL_ENABLE_AB_TOP_DIGIT_CONSTRAINT = false`, so for the AB side the boolean/range
constraint on the chunk top digit is skipped and only `digits[0]`, `digits[1]` are range-checked.
`digits[2]` is then pinned only by `product_sum = d0 + 2¹³·d1 + 2²⁶·d2` (mod M31).

*Exploit:* choose `digits[2] := (product_sum − d0 − 2¹³·d1)·inv(2²⁶) mod M31`, a free ~2³¹ value;
it feeds the AB product-digit accumulator, pushing a digit past its M31-centered bound so the
reduction recurrence `ab − qn − result + prev − 2¹³·carry` aliases 0 in M31 while nonzero as an
integer — the classic broken-bignum-AIR bug. This is the engine behind `s·u1=z_red` and
`s·u2=r` (SCALAR_SETUP, **live in the trivial path**), so those modular relations are forgeable.
(QN side is safe — its top digit *is* constrained.)

*Fix:* set the flag true (or add `row.digits[2]` to a Range membership) for the AB side, bounded
by `SCALAR_MOD_MUL_SPLIT_CHUNK_TOP_DIGIT_BOUND`.

---

## 2. Additional CRITICAL / HIGH soundness findings (per-auditor; confidence noted)

### C3 — No AIR lower bound on `s1` (and `s2_abs`) ⇒ degenerate `(s1,s2_abs)=(0,0)` certificate
**File:** `scalar/fake_glv_scalar.rs:1004-1122` (`constrain_fake_glv_scalar_general`); `s1_minus_one`
exists nowhere in the tree. The only `s1>0`/`s2_abs>0` enforcement is the prover-side hint verifier,
which a malicious prover bypasses by writing the trace directly. With `(s1,s2_abs)=(0,0)`, the
scalar-mod-mul link is `scalar·0 − 0·n − 0 = 0` (holds) and the chain proves `[0]P+[0]H=O`
trivially, leaving the hinted `H` free ⇒ ECDSA forgery.
**Confidence / caveat:** reachability in *today's* trivial-gated path is uncertain — the live
selector AIR forces `s2_abs=1` and the `FakeGlvScalar` relation binds it, which may block the
`s2_abs=0` trace. Regardless, this is a real hole in the general-path constraints and **must** be
fixed (add the spec's `s1_minus_one` column + Range check gated by `cert_active`) before the
general fake-GLV path is activated. Treat as HIGH now, CRITICAL on activation.

### C4 — Chain operands / MSB-init / LSB-correction not bound to their selectors (general path)
**Files:** `fake_glv_signed_selector_operand.rs:321-335`, `fake_glv_direct_prepared_operand.rs:312-322`,
`fake_glv_lsb_correction_operand.rs:317-330`, `fake_glv_selector_lookup.rs:984-1009`.
The spec's load-bearing bindings — `base_index == decode(selector)`, `init_base_index == 2+s1_msb+4·s2_msb`,
the `lsb00_active` gate on the `Base[2]` consumption, and canonical witnessed negation `p−y` — are
computed **host-side only**; the Selector16Decode / FinalSelector consumer emissions are dead code
and the selector lookups balance tautologically (see §4). A prover can feed a table point that does
not match the reconstructed digit. **DORMANT/trivial-gated today** (s2_abs≡1), **directly forgeable
the moment the general path is enabled.** These must land together with the selector generalization.

### H1 — Fp reduction carry bound (73 721) breaks M31 centered headroom
**File:** `fp_solinas_air.rs` consts vs `projective_air.rs:1433-1437,4395-4400`. With the wired
carry bound the per-limb expression reaches `1,207,844,864 > (M31−1)/2 = 1,073,741,823`, so the
integer congruence can alias 0 in M31. This is a *symptom* of C1 (the unbounded
`correction_product_digit` forces the bloated bound); fixing C1 shrinks the bound back.

### H2 — Raw-product-chunk reconstruction exceeds M31 headroom (projective)
**File:** `projective_air.rs:1031-1036,1401-1412`. `max_abs_expr = 1,207,697,423 > (M31−1)/2`; the
design's own `…fits_m31()` predicate returns false; concrete aliasing pairs exist. Split each chunk
into ≤2 digits per equation so the top coefficient stays under the headroom.

### H3 — Fake-GLV quotient top limb gets Range13, not Range11 ⇒ `q < 2¹³⁰` instead of `q < 2¹²⁸`
**File:** `scalar/fake_glv_scalar.rs:300-313` + `scalar_mod_mul` (Quotient role uses `range13`
exclusively; no `range11` anywhere). The spec mandates `q[9] < 2¹¹` to pin `q < 2¹²⁸`; without it the
integer scalar equation `S·s2_abs + sign·s1 − q·n = 0` loses uniqueness. Add an explicit Range11
lookup on `q[9]` gated by `cert_active` (the Range11 table already exists).

### H4 — The mandated M31-headroom "BLOCKER" artifact is not actually green
**Files:** `fp_solinas_air.rs:411-422` (test hard-codes a fictitious `carry_bound = 18` instead of the
wired 73 721, so it passes vacuously); `projective_air.rs:6105,6126,6290,6312` (headroom asserts sit
*after* width-equality asserts that currently panic, so they never execute). The spec's #1 required
safety net is dark. Make these standalone `const _: () = assert!(…)` / `#[test]` that derive bounds
from the wired tables.

### H5 — Final-check `x3` (= `r_x`) is not range-checked `< p` ⇒ mod-n acceptance binding broken
**Files:** `final_add_air.rs:1240,1330-1340`, `final_check_air.rs:236,564-568`. `x3` is bounded only
`< 2²⁵⁶`, not canonical `< p`. The single-subtraction mod-n reduction (`r_check + x_ge_n·n = x3`,
`x_ge_n∈{0,1}`) is correct only for inputs `< p`. A prover can set `x3 = x(R)+p` (quotient ≤2, passes
both range bounds) so `r_check = x(R)+(p−n) ≠ x(R) mod n`, accepting an `r` that does not equal
`x(R) mod n`. The spec explicitly requires `rx < p` (borrow witness); it is absent. Add a
canonical-LT-p check on `x3`/`r_x` gated by `active`.

### H6 — Projective / final-add Fp multiply results not forced canonical (`< p`)
**Files:** `projective_air.rs:816-832`, `fp_solinas.rs:220-230`. Results are 20×13-bit range-checked
and `≡ a·b (mod p)` but not the canonical representative (`is_less_than_modulus` is prover-side only).
Two encodings of the same field element are accepted. Latent (downstream affine export must
canonicalize); add `add_canonical_lt_fixed_bound` against `p`, or document the dependency.

---

## 3. Range / domain checks — status

* **Sound:** range-check *width isolation* (Range7/9/11/13 + signed_carry each draw an independent
  `RangeCheckRelation` instance ⇒ no "checked against the wrong-width table" hole); `canonical_lt`
  proves strict integer `<` (boolean carries + final-carry-zero + range-checked limbs/slack);
  signed-carry centered encoding round-trips within ±(M31−1)/2; `REDUCTION_MATRIX` has a genuine
  independent self-checking test; `z_red < n` + `z_limb[19]` Range9; `r,s ∈ [1,n−1]` via `r−1,s−1`
  decomps + `r<n,s<n` + nonzero check.
* **Holes:** the chunk/correction free-witness digits (C1, C2), `q[9]` width (H3), `x3 < p` (H5),
  Fp-mul canonicality (H6).
* **Robustness:** `range_checks/trace.rs:75-89` accumulates multiplicities with wrapping M31 add
  (infeasible to hit, but a `u32` counter would be safer); `scalar_mod_mul` headroom guard
  `scalar_mod_mul_fits_m31_centered()` is `#[cfg(test)]`-only — promote to a `debug_assert` on the
  build path.

---

## 4. State of implementation (what is live vs dormant)

* **The fake-GLV layers are at different stages.** The **scalar-equation AIR is general and live**
  (`fake_glv_scalar.rs:248` → `constrain_fake_glv_scalar_general`, real `S·s2_abs+sign·s1−q·n=0`
  proved through the live ScalarModMul links). The **selector-reconstruction AIR is still trivial**
  (`fake_glv_selector.rs:192` → `constrain_selector_from_trivial_scalar`, pins `s2_abs=1`). Every live
  monolithic prove/verify test uses `from_inputs_with_trivial_fake_glv_hints`; `from_inputs_with_arbitrary_…`
  and the real-p256 e2e are `#[ignore]` "pending selector AIR generalization". Net: end-to-end generic
  signatures are not yet provable — the selector/chain is the remaining trivial piece, not the scalar math.
  Because the general scalar AIR *is* live, findings C3 (`s1≥1`) and H3 (`q[9]` Range11) are gaps in live
  general-path constraints (currently masked by the selector pinning `s2_abs=1` and `S≠0`), not dormant.
* **Selector lookups (Selector4x4 / Selector16Decode / FinalSelector) are DORMANT** — committed/proved
  in a separate slice whose balance is a host-side tautology over `selector_requests`; they are *not*
  consumed inside the monolithic STARK, so the decode/init-base bindings (C4) are absent from the live
  circuit. When the general path lands, these three relations must be added to `relation_balances()`
  or they become committed-but-unbalanced lookups.
* **Verifier takes no external public-input argument** (`verify_current_air_monolithic`): the statement
  is whatever sits in `proof.claim.public_inputs`. Mutating it desyncs Fiat-Shamir (FRI rejects), so
  the *proof* is bound — but a **caller must compare `proof.claim.public_inputs` against the expected
  `(msg,r,s,pubkey)` out-of-band**, or accept a valid proof of a different statement. Document loudly or
  add an `inputs: &[EcdsaVerifyInput]` equality check.
* **Low-S is intentionally not enforced** (spec-confirmed): signatures remain malleable to `(r, n−s)`.
  Property gap, not a soundness bug — flag to consumers who need strong non-malleability.

---

## 5. What is sound / notable strengths

* **Relation-balance completeness is sound.** Every relation emitted by a monolithic component is
  folded into exactly one zero-gated entry of the single-source-of-truth `relation_balances()`
  (proof.rs:1051, 28 entries); `verify_balanced` requires each = 0. No emitted-but-unbalanced relation
  in the live path. The `#[cfg(test)] liveness_witnesses()` even guards the "0+0 looks balanced but is a
  dead link" case — security-aware design (the stwo-cairo lesson). *Minor:* `liveness_witnesses` could
  add the `ScalarSetupOutput` / `CertScalarInput` / `FakeGlvScalar` boundary edges.
* **Fiat-Shamir order is correct and identical prover/verifier;** relation challenges (`α,z`) are drawn
  strictly *after* the base-trace commitment; every claim/interaction-claim field is mixed.
* **Native EC formulas are correct.** `rcb_double`/`rcb_mixed_add` (RCB Alg 6/5, `a=−3`) were
  machine-verified for P+Q, P+P, P+(−P)→(Z=0,Y≠0), O+P, DOUBLE(O)→(0,1,0); `(0,0,0)` is forbidden;
  exceptional cases complete. (But the AIR doesn't yet *constrain* the EC sequencing — see note below.)
* **Public-input binding is structurally sound.** SCALAR_SETUP consumes the public tuple
  (`+sig_active`) into the *same* limbs that feed digest reduction, `r<n`/`s<n`, the scalar links, and
  the yielded `ScalarSetupOutput`/`PublicKeyPoint` — no "consume A / compute B" split. Public-data
  provider sum is derived from the verifier-bound claim, not prover trace.
* **Final add / check core is correct:** the acceptance equation `r_check = x(R) mod n` is present,
  integer-level, gated, with `r` bound to public `r` and `R = H1+H2` linked from the chain; `R≠O`
  enforced; pubkey validated on-curve and bound to the cert-1 base. (Modulo H5/H6.)
* **`mul_id` namespacing** (compile-time constants, disjoint setup vs fake-GLV ranges) prevents
  cross-multiplication collisions in the shared scalar engine.

> Note (pass 2 — now confirmed as C5, not "worth confirming"): the projective AIR constrains only
> "13 self-consistent Fp multiplications." For `final_add` and `public_key_curve` the RCB formula
> bindings exist (those consumers do bind result limbs per step). For the **fake-GLV scalar-mul
> ladder they do not** — the ladder never consumes the mod-p mul engine, so the per-step EC
> add/double outputs are free witnesses. See C5 above. A prover can therefore choose the entire point
> sequence of the scalar multiplication.

---

## 6. Optimization notes (secondary — defer until sound)

Optimizing an incomplete, unsound circuit is premature; the missing constraints (C1, C3, C4) will add
columns/relations and change the cost profile. Once sound, the levers worth measuring:

* `final_add_air.rs:316,1208-1210` — `MUL_X1_SQUARED` runs on every active row but is consumed only on
  the doubling branch; gate or drop the idle multiply.
* The Fp reduction currently needs an extra free `correction_product_digit` column per digit; building
  the correction accumulator (C1) lets the carry bound shrink dramatically (H1), reducing the
  signed-carry table width and LDE work across the projective engine.
* `finalize_logup` is used almost everywhere; components with ≥6 emissions/row (e.g. cert_bind=6,
  scalar selector lookups=6) could use `finalize_logup_in_pairs` to roughly halve interaction columns
  if the degree budget allows — measure first.
* Relation arities hard-coded as macro literals (`PreparedPointRelation, 44`; `PublicEcdsaInstance, 101`)
  rather than derived from the limb consts — couple them with a `const _` assert to prevent silent drift.

---

## 7. Recommended remediation order

1. **C1** — build the correction-product accumulator relation (unblocks H1, H4; restores Fp soundness).
2. **C2** — constrain/range-check the AB chunk top digit (restores `s·u1`,`s·u2`).
3. **C5** — bind every fake-GLV ladder step's `output` to `rcb_double`/`rcb_mixed_add` of its inputs
   via the `projective_air` mod-p mul engine (as `final_add` does). Largest single fix; restores the
   actual EC scalar multiplication. Without this, C1/C2 fixes still leave `R` forgeable.
4. **H5, H6, H3** — canonical `< p` on `x3` and Fp-mul results; Range11 on `q[9]`.
5. **H2, H4** — split raw-product chunks to ≤2 digits; make the headroom asserts real and green.
6. **C3, C4** — the s1≥1 bound and the selector-decode / init-base / lsb00 / canonical-negation
   bindings, landed together with the general fake-GLV (non-trivial s2) generalization, and wire the
   three selector relations into `relation_balances()`.
7. Then: re-run the per-component soundness audit, add adversarial tests for each fixed invariant, and
   only then revisit optimization.

---

## Appendix — per-subsystem posture

| Subsystem | Posture | Headline |
|---|---|---|
| range_checks + REDUCTION_MATRIX | sound | width isolation correct; matrix self-checked |
| Fp Solinas reduction (`fp_solinas*`) | **broken (C1)** | free `correction_product_digit` |
| scalar_mod_mul (mod n) | **broken (C2)** | AB `digits[2]` unconstrained; rest sound (canonical results, mul_id isolation) |
| scalar setup + cert_bind | sound (delegates) | public binding intact; modular soundness inherited from scalar_mod_mul |
| fake_glv_scalar | hole (C3, H3) | no `s1≥1`; `q[9]` Range13 not Range11 |
| fake-GLV EC ladder (chain / ec_source) | **broken (C5)** | per-step EC add/double outputs are free witnesses; mod-p mul engine never wired into the ladder |
| selectors + chain operands | dormant holes (C4) | decode/init/lsb/negation bindings host-side only; selector AIR trivial-only |
| prepared_table + point bus | sound | use_count Range7 + zeroed on inactive; pinning balanced; canonical-∞ enforced |
| projective EC engine | **broken (C1) + H2** | native formulas correct; AIR reduction forgeable; headroom violated |
| final add/check + pubkey curve | hole (H5, H6) | acceptance eq present & bound; `x3`/results not canonical `< p` |
| proof orchestration | sound | balance completeness, FS order, public binding all verified; live path trivial-only |
