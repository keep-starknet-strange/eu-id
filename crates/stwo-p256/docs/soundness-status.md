# P-256 STWO AIR — soundness status

**Updated:** 2026-06-11 (post hinted-modmul rewrite, consumer folds, γ-digest
reshape, operand dedup, schoolbook-silo deletion).

This replaces the full 2026-06-08 audit (`soundness-audit.md`, see git
history): that document's findings referenced the now-deleted schoolbook
silo and are almost entirely resolved or moot. This page tracks what is
actually open against the current architecture.

## OPEN findings

### O1 — public-input binding gap (CRITICAL, verifier-level)
The verifier never independently recomputes the public-instance /
ecdsa-result LogUp provider sums from the instances it was handed; it uses
prover-supplied claimed sums. The proof is therefore not bound to the
`(h, r, s, pub)` the verifier believes it is checking — signature acceptance
is forgeable at the statement level. Fix: recompute
`ecdsa_result_provider_claimed_sum` (and the public-instance provider terms)
verifier-side from the instances and reject on mismatch.

### O2 — preprocessed root unpinned (CRITICAL, verifier-level)
The verifier trusts the prover's preprocessed-tree commitment. Range tables,
schedule columns (including every γ-digest tall schedule, whose soundness
argument explicitly leans on "preprocessed is the anchor"), and constants are
prover-chosen. Fix: the verifier must recompute (or pin a constant root for)
the preprocessed tree from the proof claim and compare.

### O3 — fake-GLV hint point R not proven on-curve (HIGH)
The ladder result point (the hint `R`) gets no on-curve check, so the RCB
complete-formula soundness theorem's precondition is unmet (degenerate free
output). Fix: one curve-membership check on `R` (the
`public_key_curve`-style identity, or fold into `final_add`).

### O4 — fake-GLV quotient top limb range (MEDIUM, was H3)
The scalar-equation quotient's top limb is Range13-checked, not Range11, so
`q < 2¹³⁰` instead of the spec's `q < 2¹²⁸`. The RANGE11 table machinery
exists (`range_checks::RANGE11_BITS`) but is not applied. Verify whether the
slack actually breaks uniqueness of `S·s2_abs + sign·s1 − q·n = 0` with the
current bounds; if so, add the Range11 use on the top limb.

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
