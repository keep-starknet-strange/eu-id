# WO-G4 — ECDSA-verify circuit inventory + gate count (the gate-count GATE)

**Status:** gate artifact (S4-lite Phase-1, #6). Blocks BL4. Architect ack required at bottom.
**Gate:** ≤ 35,000 quads for one ECDSA-P256 verify, native F_p256, EVERY hint bound.
**Semantics source:** `crates/stwo-p256/src/types.rs::EcdsaVerifyInput` (z = `message_hash`,
sig `r,s`, pubkey `Qx,Qy`). Curve: `y² = x³ + ax + b`, a = −3, b = P256_B. Field prime p, order n
(P256_MODULUS / P256_ORDER). **z, r, s, u1, u2 are scalars mod n; point coords are mod p.**

## Conventions
- "quad" = one degree-≤2 multiplication gate over F_p256 (Longfellow's accounting: one field mul = one gate).
- Limb decomposition: 256-bit values as 20 × 13-bit limbs (LIMB_BITS=13, matches the M31 side). Booleanity
  is per-**bit**; a 13-bit limb range = a 13-gate bit-decomposition, so a full 256-bit range = 256 bit-gates.
- Point mul is **hinted double-and-add**, 256 steps, **affine** coords (§ inversion below). Windowing is
  deferred to BL4 as an optional gate-count optimisation; this inventory is the sound floor (double-and-add),
  which already fits the budget, so we spec the floor and leave width to the implementer.

## mod-n arithmetic in an F_p circuit (the real design point)
F_p circuit gates compute mod p. Scalar relations are mod n. We **do not** emulate mod-n natively; we hint
the reduced result and prove the reduction. For any scalar relation `a·b ≡ c (mod n)` (with a,b,c < n):
the prover witnesses `c` and a quotient `q` s.t. the **integer** identity `a·b = q·n + c` holds, then the
circuit checks that identity **over the integers via limb arithmetic embedded in F_p** (products of 13-bit
limbs never overflow p, so limb-wise schoolbook mul + carry chain is exact in F_p), plus `c < n` and
`q < n` canonicality. This is Longfellow §4's method: mod-n is a hinted div-with-remainder, not field ops.

## Constraint inventory
| # | Constraint family | What it enforces | quads | Witnesses it binds | deg |
|---|---|---|---|---|---|
| C1 | Input limb decomposition | z,r,s,Qx,Qy each = Σ bᵢ2^{13i}; recompose = felt | 5×20 = 100 | z,r,s,Qx,Qy limbs (5×20) | 2 |
| C2 | Input canonicality | r,s ∈ [1,n); z reduced; Qx,Qy < p | 5×~40 = 200 | (reuses C1 limbs) | 2 |
| C3 | sinv well-formed | s·sinv ≡ 1 (mod n): limb-mul = q·n+1, sinv<n,q<n | ~430 | sinv, q_inv | 2 |
| C4 | u1 = z·sinv (mod n) | z·sinv = q₁·n + u1; u1<n, q₁<n | ~430 | u1, q₁ | 2 |
| C5 | u2 = r·sinv (mod n) | r·sinv = q₂·n + u2; u2<n, q₂<n | ~430 | u2, q₂ | 2 |
| C6 | u1,u2 bit decomposition | u1,u2 = Σ βⱼ2^j; each βⱼ boolean | 2×256 = 512 | u1_bits, u2_bits (512) | 2 |
| C7 | G-table on-curve | fixed 2G..? — **preprocessed/public**, no witness | 0 | — | — |
| C8 | Q-table on-curve | each precomputed iⱼ·Q table point on curve | (windowless: 0) | — | 2 |
| C9 | u1·G ladder | 256 double-add steps, group-law quads (§below) | ~256×26 = 6,656 | 255 accum pts (×2 coord)=510 | 2 |
| C10 | u2·Q ladder | 256 double-add steps, group-law quads | ~256×26 = 6,656 | 255 accum pts=510 + Q on-curve | 2 |
| C11 | final add R = u1G ⊕ u2Q | one affine add, group-law quads | ~30 | R.x,R.y + slope-inv | 2 |
| C12 | every-point on-curve | y²=x³−3x+b for EVERY witnessed accum + R | ~512×4 = 2,048 | (binds C9/C10/C11 outputs) | 2 |
| C13 | slope-denominator inverses | each dᵢ·dᵢ⁻¹=1 (batch-inverted hint bound) | ~514 | 514 slope-inv hints | 2 |
| C14 | final check r ≡ R.x (mod n) | R.x = k·n + r'  with r'=r; canonicality k∈{0,1} | ~45 | k (reduction flag), r' | 2 |
| C15 | exception guards | u1G, u2Q, R ≠ 𝒪 flags = 0 (see policy) | ~10 | infinity flags (bound=0) | 2 |
|   | **TOTAL** | | **≈ 27,471** | | |

**Ladder step (C9/C10) breakdown per bit:** a double (slope λ=(3x²−3)/2y → ~6 quads incl. inverse-mul
binding) + a conditional add of the ladder base selected by the bit (~14 quads: bit-multiplexed addend,
slope, x₃=λ²−x₁−x₂, y₃=λ(x₁−x₃)−y₁) + on-curve deferred to C12. ~26 quads/step is the accounting anchor;
Longfellow's 24,477 total is the sanity check we land under.

**Budget:** ≈ 27.5k quads ≤ 35,000. **PASS with ~7.5k slack** for windowing carry-corrections or a
projective rewrite of the ladder. If BL4 measures > 33k, mailbox before proceeding.

## Witness ledger (no-unbound-hints law, auditable)
| Witness | count | bound-by |
|---|---|---|
| z,r,s,Qx,Qy limbs | 100 | C1 (recompose) + C2 (canon) |
| sinv | 1 | C3 |
| u1, u2 | 2 | C4, C5 |
| q_inv, q₁, q₂ (mod-n quotients) | 3 | C3, C4, C5 (each q<n) |
| u1_bits, u2_bits | 512 | C6 (booleanity β²=β) + tie to u1,u2 via Σ |
| u1G ladder accum pts | 510 | C9 (group law) + C12 (on-curve) |
| u2Q ladder accum pts | 510 | C10 (group law) + C12 (on-curve) |
| Q-table pts (if windowed) | 0 (double-add: none) | C8 (on-curve) — N/A for floor |
| slope-denominator inverses | 514 | C13 (d·d⁻¹=1) |
| R.x, R.y | 2 | C11 (group law) + C12 (on-curve) |
| reduction flag k, r' | 2 | C14 |
| infinity flags | 3 | C15 (=0) |
| **Total witnessed** | **≈ 2,159** | (Longfellow: 1,085/sig — we are ~2× the floor, all bound; windowing will cut the ladder witnesses ~2×) |

Every row above names its binding constraint. Any witness added in BL4 not in this ledger ⇒ STOP + mailbox.

## Edge / infinity policy (measure-zero cases)
**Policy: reject-and-regenerate hints — NOT constraint support.** The exceptional inputs are (a) u1G = 𝒪
or u2Q = 𝒪 (u1 or u2 ≡ 0 mod n), (b) u1G = ±u2Q (final add hits doubling or infinity), (c) a ladder step
hitting P = −P (vertical slope, dᵢ = 0). These are measure-zero over honest inputs.
- **Completeness:** the prover's hint generator detects any exceptional intermediate and, being prover-local
  and free to choose the ladder base representation (windowing offset / blinding of the accumulator start),
  re-derives a non-exceptional trace. The affine group-law formulas are then always well-defined; every dᵢ
  is invertible so C13 is satisfiable. Justification: adding constraint-level support for infinity (a
  select over the complete/incomplete formula, per step) would ~double C9/C10 and buy nothing — an honest
  verifier's real signatures never hit these, and a malicious prover gains nothing (a forged sig still must
  satisfy C11/C14 with real coordinates). C15's flags are pinned to 0, so a prover **cannot** smuggle an
  infinity through; it must instead present a non-exceptional trace, which the reject-and-regenerate hint
  gives it for all valid witnesses. This is strictly the fake-GLV lesson applied: no free/degenerate output.
- **Soundness note:** C15 = 0 pinning is what makes reject-and-regenerate sound rather than a completeness
  hole — the circuit is unsatisfiable on an infinity, so "regenerate" is the only path, not "skip a check."

## Soundness lessons discharged here
- **fake-GLV on-curve gap** (`project_p256_fakeglv_hint_not_on_curve`): C12 puts EVERY witnessed point —
  ladder accumulators, table points, and R — on the curve. No point enters a group-law quad unconstrained.
- **final r_x canonicality** (C5/mixed-sign lesson): C14 proves R.x reduces to r mod n with an explicit
  reduction flag k ∈ {0,1} (R.x < n ⇒ k=0; the R.x ∈ [n, p) "+n wrap" case ⇒ k=1, r = R.x − n), booleanity
  of k pinned. Both the canonical and the wrapped case are covered; mixed-sign is impossible because r,r'
  are proven < n by C2/C14.

---
- [x] **Architect ack:** inventory total ≤ 35k with every hint bound and edge policy accepted. — fable, 2026-07-03, **with the Q-019/Q-021/Q-022 amendments below (normative where they differ from the table above):**
  - C9/C10 are **256 uniform MSB-first steps from a blinded start** `acc_0 = B = (i+1)·G` (public blind index `i`; verifier recomputes `B` and `D = 2^256·B` host-side), plus one correction add `⊕(−D)` per scalar. Stored accumulators 255 → **256 per scalar**, plus corrected endpoints S₁,S₂. Canonical spec: `../mailbox/answers/Q-022.md`.
  - C13: 514 → **1027** (a uniform mux'd step consumes both the double and the add denominator every step; +1 correction denom per scalar, +1 final add).
  - Witness ledger total 2159 → **2680** (LAYOUT v2 in the Q-022 answer). Public inputs gain i₁,i₂ and B₁,D₁,B₂,D₂ coordinates.
  - Revised estimate ≈ **28.0k** quads; a per-step re-derivation lands ~11–13 quads (26 is ~2× conservative). Gate unchanged: builder-measured count ≤ 35k, mailbox if > 33k.
  - C15 completeness argument (blinded-start regeneration): written in Q-022 §3; the unbounded public index means no exhaustible blind list; C15=0 pinning keeps reject-and-regenerate a completeness mechanism, not a soundness hole.

---
## Architect pre-review notes (2026-07-03, fable)
- **C14 wrap flag: CONFIRMED sound.** n > 2^255 ⇒ 2n > 2^256 > p ⇒ R.x < p < 2n; k ∈ {0,1} suffices. No wider quotient needed.
- **C9/C10 (~48% of budget): review-first item at ack time.** The 26 quads/step estimate must be re-derived against BL2's actual gate charging (slope inverse + conditional-add mux) before the 35k PASS is trusted; a 2x error here is the only threat to the gate.
- **C15 edge policy: the blinded-accumulator completeness claim needs a written argument** (random blinding start ⇒ each exceptional event u1≡0 / u1G=±u2Q / per-step P=−P has negligible probability over the blinding; regenerate on failure). Two paragraphs, part of the ack review — the mechanism is standard but "asserted" is not "argued".

## RESULT (builder-measured, 2026-07-04, S4-lite implemented families)
Current implemented BL2 ECDSA circuit families build to 9,903 sparse quad terms. This is below both the 33,000 mailbox threshold and the 35,000 gate.

Machine-readable (parsed by gates.rs):
- measured_quad_count: 9903
