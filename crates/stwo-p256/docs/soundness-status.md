# P-256 STWO AIR — soundness status

**Updated:** 2026-06-11 (O1 closed; post hinted-modmul rewrite, consumer folds, γ-digest
reshape, operand dedup, schoolbook-silo deletion).

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

### O2 — preprocessed root unpinned (CRITICAL, verifier-level) — needs a refactor
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

### O3 — fake-GLV hint point R not proven on-curve (HIGH) — needs analysis
The RCB complete-addition formulas are only sound for on-curve inputs.
Re-scoping (2026-06-11): the two ladder BASE points are the generator G
(public constant, on-curve) and the public key Q (now on-curve-checked by
the folded `public_key_curve` component + the S2 canonicality gate), and
the prepared-table points are derived from the base via in-AIR EC ops
(pinned by `CertBaseRelation` + `PreparedTableCanonicalRelation`). So the
naive "base not on-curve" gap appears already covered. The precise residual
— whether any intermediate accumulator or the Garaga hint point can be
forced off-curve while satisfying every other constraint — requires
re-deriving the fake-GLV soundness argument against the current component
graph before adding a check (an unnecessary on-curve gate is pure cost).
Deferred pending that derivation.

### O4 — fake-GLV scalar magnitude top-limb range (MEDIUM, was H3) — needs analysis
`s1`, `s2_abs`, and the quotient `q` of the integer scalar equation
`k·s2_abs − q·n ± s1 = 0` are stored in `FAKE_GLV_SMALL_LIMBS` 13-bit limbs
with higher limbs zeroed; the TOP small limb gets Range13, not Range11, so
each value can reach ~2¹³⁰ instead of the spec's < 2¹²⁸. Whether the ~2-bit
slack is exploitable is subtle and unresolved: (i) `q` is DETERMINED by
`(k, s2_abs, s1)` via the equation, so its bound is implied by `s2_abs`'s —
the binding constraint is `s2_abs < 2¹²⁸`, not `q`; (ii) any VALID
decomposition (even oversized) computes the same `k·base`, so the bound is
about completeness/window-count, NOT soundness — UNLESS the fixed-width
fake-GLV ladder silently truncates the top 2 bits (then a 130-bit `s2_abs`
proves a different scalar than the chain processes). Resolving (ii) needs
the ladder window count vs `FAKE_GLV_SMALL_LIMBS·13` checked against the
fake-GLV spec. If a real gap, the minimal fix is a Range13 use on `4·top_limb`
(⟺ top_limb < 2¹¹) — reuses the existing range13 table, no new provider.

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
