# P-256 STWO AIR — soundness status

**Updated:** 2026-06-11 (O1 closed; O2/O3/O4 independently re-verified against
the current code — O2 CONFIRMED critical, O3 CONFIRMED a real gap, O4 REFUTED
as benign; post hinted-modmul rewrite, consumer folds, γ-digest reshape,
operand dedup, schoolbook-silo deletion).

This replaces the full 2026-06-08 audit (`soundness-audit.md`, see git
history): that document's findings referenced the now-deleted schoolbook
silo and are almost entirely resolved or moot. This page tracks what is
actually open against the current architecture.

## OPEN findings

### O1 — public-input binding gap — ✅ CLOSED (2026-06-11)
The verifier now recomputes the `PublicEcdsaInstance` and `EcdsaResult`
provider sums (public-data initial-LogUp claims, no committed trace) from
`claim.public_inputs.instances` after drawing the relation elements, then
runs the balance — so the proof is tied to exactly the instances the
verifier holds. The consumer sides are STARK-bound committed components.
Tests: `…rejects_unbound_public_key`, `…rejects_mutated_public_r`,
`…ignores_prover_ecdsa_result_provider_sum`. (stwo-cairo's Rust verifier
has the SAME gap; the equivalent recomputation lives in its
`lookup_sum`/`public_data.logup_sum`.)

**Caller-argument binding — ✅ CLOSED (2026-06-12, uncommitted).** O1 ties the
proof to its OWN embedded instances, but `verify_current_air_monolithic` used to
take only the proof and return `Result<(),_>`, so a relying party that trusts
`Ok(())` would accept a proof of ANY signature the prover embedded. The verifier
now takes `expected_instances: &[PublicEcdsaInstance<M31>]` and rejects with
`P256ProofError::PublicInstanceMismatch` if they differ from the embedded
instances, before any proof work. Test:
`current_p256_monolithic_verifier_rejects_mismatched_expected_instances`.

### s2_sign_bit "missing in-AIR constraint" — ❌ FALSE POSITIVE (2026-06-12)
A prior audit claimed active certs require `s2_sign_bit==1` in-AIR. **Do NOT add
`cert_active·(s2_sign_bit−1)=0`** — it would reject ~55% of honest signatures.
`s2_sign_bit` is the Garaga lattice sign, input-dependent (probe: 24×0 / 20×1 of
44 scalars; the real `p256`-crate fixture is bit=0 on both certs). The bit is
already pinned by the ScalarModMul `selected_s1` identity + 128-bit bounds
(`fake_glv_scalar_hints_reject_flipped_sign`). Disproving this surfaced O5 below.

### O5 — final_add mixed sign bits — ✅ CLOSED (2026-06-12, uncommitted)
Fixed: `final_add` consumes each cert's proven `s2_sign_bit` via a new
`FinalAddSignRelation` (provider `fake_glv_scalar`, gate `−cert_active`; consumer
`final_add`, gate `active·(1−r_i.inf)`; balance entry `FinalAddSign`) and orients
`R_2` by `d = b1 ⊕ b2` (witnessed `r2p_y` via a gated modular negation), running
the chord/tangent add on `(R_1, (r2.x, r2p_y))` so it binds `x(h_1+h_2)`. Test
`current_p256_monolithic_proves_mixed_sign_bit_signature` proves+verifies a valid
`b1 ≠ b2` signature; full `stwo-p256` lib suite: 301 passed. Original analysis
below.

### O5 (original) — final_add mixed sign bits — COMPLETENESS bug
`final_add` binds `r_x = x(R_1+R_2)` (signed hints), which equals the ECDSA
target `x(h_1+h_2)` only when `b_1==b_2`. When the two certs decompose to
opposite signs (`b_1≠b_2`, ~50% of real signatures since `u_1,u_2` are
independent), `R_1+R_2 = ±(h_1−h_2)` and `r_x` is wrong — a valid mixed-bit
signature fails to prove with `RelationImbalance { FinalAddOutput }` (confirmed
empirically). NOT a forgery; the existing real-signature test only passes because
its fixture is `b_1==b_2==0`. Fix (designed): consume each proven `b_i` via a new
`FinalAddSignRelation` provided by `fake_glv_scalar`, conditionally negate `R_2`
by `d=b_1⊕b_2`, and add `R_1 + (-1)^d R_2` (x = x(h_1+h_2)). See the memory note
`project_p256_final_add_mixed_sign_bug`.

### O2 — preprocessed root unpinned (CRITICAL, verifier-level) — needs a refactor
**Re-verified 2026-06-11 — CONFIRMED real.** `verify_current_air_monolithic`
hands the PCS `commitment_scheme.commit(stark_proof.commitments[0], …)`
(`proof/mod.rs:2967`) — prover root, shape-only `dummy_log_degree_bounds`, no
constant pin, no verifier-side regeneration. The range provider's `evaluate`
adds ZERO algebraic constraints on the table value column
(`range_checks/component.rs:14-17,39-49`: "this component does not constrain
the table contents"); the values are pinned ONLY by membership in the unpinned
tree. Concrete forgery confirmed: commit a `range13` value column that also
holds `2²⁰` (multiplicity 1); an out-of-range trace limb `= 2²⁰` then closes
the range LogUp (provider/consumer cancel) with every polynomial constraint
satisfied. The signed-carry provider only constrains `active` booleanity and
padding multiplicity — its `value` column is equally free.

The verifier registers the prover's preprocessed-tree root
(`stark_proof.commitments[0]`) on trust; it never reconstructs the tree.
Empirically (probe, 2026-06-11) the preprocessed root is IDENTICAL across
two small-scalar signatures but DIFFERS for a real signature at the same
log sizes — so the tree is witness-dependent, NOT a single circuit constant.

Root cause: the preprocessed tree mixes (a) genuinely-fixed, dangerous
columns the prover could swap — range13/9/7 + signed-carry TABLE value
columns (e.g. a forged range13 table that contains 2²⁰ makes an
out-of-range limb pass), and (b) witness-dependent SCHEDULE columns
(hinted-mul `source_index`/`mul_index`/`active`, scalar-mod-mul schedules)
that vary with the ladder op pattern. The schedule columns are ALSO bound
by the `ProjectiveRcbMulResult` / range balances (a forged schedule
unmatches the yields), so the residual unconstrained risk is specifically
the fixed TABLE columns — but they share one Merkle root with the
witness-dependent schedules, so a constant pin (stwo-cairo's approach) does
not apply and naive claim-regeneration fails (the proof claim carries only
log sizes, e.g. `HintedMulProofClaim { log_size }`, not the per-row
schedule).

Two correct fixes, both real work: (1) move the witness-dependent schedule
columns OUT of preprocessed into the (committed + AIR/balance-constrained)
base trace, leaving preprocessed = fixed tables → then pin a constant root;
or (2) carry the schedule in the proof claim so the verifier regenerates
the whole preprocessed tree and recomputes the root. (1) is the clean
stwo-cairo-style architecture. Provider-fleet consolidation (4×2¹⁸ → 1)
would also shrink the regeneration cost under (2).

### O3 — fake-GLV hint point R not proven on-curve (HIGH) — CONFIRMED real (2026-06-11)
The RCB complete-addition formulas are only sound for on-curve inputs. The
derivation that was "deferred" is now done, and the residual gap is REAL.

The two ladder BASE points are fine: G is a hard-coded literal (`P256_GX/GY`,
`P256_3GX/3GY`, on-curve by construction, independent of O2) and Q is proven
on-curve in-AIR by `public_key_curve` (`y² + 3x ≡ x³ + b mod p`, bound to the
public-input instance). The prepared-table *base* multiples are also fine: `2P`,
`3P` are in-AIR RCB images of P (`bind_double_formula`/`bind_mixed_add_formula`,
`prepared_table/air.rs:483-541`) ⇒ transitively on-curve.

The gap is the hint point **R** (the ladder output whose `x` becomes ECDSA `r`).
R is a FREE witness: it enters as `PinPoint::Lhs` of the `DoubleR` row, pinned
as the canonical `ROLE_R` provider (mult −3, `prepared_table/mod.rs:354`) — its
value is simply whatever the prover writes there. R is only Range13-checked
(limb canonicality); it is NEVER given a `y² = x³ − 3x + b` membership
constraint. Every "R-multiple" (`2R`,`3R`,`−R`,`−R3`) is an RCB image of this
one free R. The fake-GLV closing identity IS enforced
(`is_last·(acc_after − r3) = 0`, `chain/continuity.rs:185`: the windowed
accumulator must equal `3R` on the last row), but it constrains a SUM OF RCB
IMAGES to equal `3R`. RCB add/double are rational maps on all of 𝔽_p² that
equal the group law only on-curve, so `acc = 3R` is a polynomial system in the
free `(x_R, y_R)` whose solution variety is NOT contained in the curve —
off-curve solutions exist, each giving an `x(R₁+R₂)` the verifier accepts as
`r`. This is the classic invalid-curve / missing-point-validation forgery, and
unlike `3P` (= in-AIR `P + 2P`) R has NO in-AIR derivation from G/Q to make
on-curve-ness transitive; the closing identity runs the wrong direction.

Minimal fix: one in-AIR `y² = x³ − 3x + b` check on each active R (reuse the
`public_key_curve` recipe — 4 hinted muls + a signed-carry curve identity, no
new provider). Distinct from the closed C5 (EC-arithmetic binding); O3 is the
orthogonal point-MEMBERSHIP gap on R.

### O4 — fake-GLV scalar magnitude top-limb range — ❌ REFUTED / benign (2026-06-11)
The premise was wrong. `s1`/`s2_abs` are NOT stored as range-checked 13-bit
limbs at all (grep for `range13|range11` across `fake_glv/scalar` and
`fake_glv/selector` returns nothing). They are reconstructed bit-by-bit from
the selector witness (`selector/air.rs:704-731`): bit 0 + 63 two-bit chunks
(bits 1..126) + bit 127, every bit booleanity-constrained
(`selector/air.rs:593`). Max bit = 127 ⇒ structurally `< 2¹²⁸`, with the top
small limb covering bits 117–127 = exactly 11 bits — i.e. the in-AIR bound is
already `< 2¹¹` on the top limb, *stronger* than the doc's feared Range13.

No truncation, so no soundness gap: the ladder reads the SAME `row.selectors`
columns that the equation reconstructs from
(`active·(selector − s1_chunk − 4·s2_chunk) = 0`, `selector/air.rs:597-598`),
so the proven scalar and the multiplied scalar share one bit-source — the
ladder cannot process a truncated scalar. `q` is determined by the equation
`S·s2_abs ± s1 − q·n = 0` (enforced via the per-cert `scalar_mod_mul`
instance) from the already-bounded `(s2_abs, s1)`. `require_128_bit_bound`
(`scalar/air.rs:637-654`) is native belt-and-suspenders, not the binding.
Residual is cosmetic only: `q`'s top quotient limb in `scalar_mod_mul` rides
Range13 not a dedicated Range11, but `q` is pinned by the bounded operands, so
the 2-bit headroom is not soundness-exploitable. No fix required.

## Resolved since the 2026-06-08 audit
- **C1/C2** (free `correction_product_digit`, unconstrained AB `digits[2]`):
  closed 2026-06-10; C1's silo instance is additionally moot — the schoolbook
  silo is deleted and every mod-p mul is proven by the hinted-mul component
  (channel-drawn z, carry-polynomial identities, integer-lifting worksheet in
  the component docs).
- **C5** (unconstrained ladder ⇒ forgeable `R`): closed via the C5 plumbing —
  EC rows consume the hinted provider's wide mul tuples, coordinate formulas
  re-proven in-AIR on both projective-source consumers (Double + MixedAdd
  binders), operands pinned by the consume↔provider balance (operand dedup).
- **C3** (zero-scalar certificates): semantics settled (S3).
- **C4** (chain operands / selector binding): closed (Gaps A/B/C).
- **H5** (`r_x` not `< p`): closed — in-AIR canonicality check + the x+p
  forgery test.
- **H6** (pub-key canonicality): closed — verifier gate (subject to O1/O2).
- **H1/H2/H4** (silo headroom items): moot — the schoolbook silo is deleted.

## Standing analysis artifacts
- `docs/gamma-digest-design.md` — γ-digest worksheet (binding chain, S-Z
  bound, schedule-anchor requirement, degree table, adversarial plan).
- Hinted-mul integer-lifting bounds: see `components/hinted_mul` module docs.
- `tasks/lessons.md` — accumulated implementation rules (degree ceiling:
  ≤ 3 at `log_size + 1`, logup batch ≤ 2, empirically validated).
