# EC Coprocessor: Design and Soundness

Status: draft, 2026-07-06. Covers `crates/eu-id-ec-coprocessor` and its binding into the
mdoc prover (`crates/eu-id-prover/src/mdoc_mac.rs`, `mdoc.rs`) as of branch
`feat/proof-reductions` @ `9e1ac686` plus working-tree changes (the C-p4b-blind-claim
fix in `ligero.rs` and the new `circle_fft.rs` module, both uncommitted).

---

## 1. Why a coprocessor exists

The main mdoc proof is a stwo STARK over M31 (Mersenne-31). Proving P-256 ECDSA
verification *inside* that AIR requires emulating 256-bit prime-field arithmetic with
small limbs — measured at ~12.5k trace columns, the single largest cell-volume item in
the pipeline.

The coprocessor removes that cost by proving the ECDSA statements in a **separate proof
system whose native field is the P-256 base field Fp itself**. Curve arithmetic then
costs one quadratic gate per field multiplication instead of hundreds of limb columns.
The design is Longfellow-style: a layered arithmetic circuit, proven with a GKR-type
sumcheck, with the witness committed under a Ligero polynomial commitment
(Reed-Solomon + Merkle; a circle-FFT encoding front-end that removes the dominant
RS-encode cost is specified and partially landed — §5.6).

That leaves one problem: the ECDSA public inputs (message hashes, public keys) are
*witnesses of the outer M31 proof*. Two independent proofs about "some" values prove
nothing unless the values are shown equal across proofs. That cross-proof binding is
done with a GF(2^128) polynomial-evaluation MAC (§7), chosen over a repo-native MLE
binding argument after a cost comparison (the byte-vs-limb representation gap made the
direct polynomial argument more expensive than a 128-bit MAC per bound value).

The trust chain, end to end:

```
outer M31 STARK                          coprocessor (this crate)
┌────────────────────────┐              ┌────────────────────────────┐
│ SHA-256 of MSO → z     │   6 MAC tags │ ECDSA circuits C1..C14-15  │
│ device key Q  (witness)│◄────────────►│ over Fp (P-256 base field) │
│ MAC consumer AIR       │  (a_p ⊕ a_v)·x │ GKR sumcheck + Ligero PCS │
└────────────────────────┘              └────────────────────────────┘
        both proofs share one Fiat-Shamir ordering: commitments
        first, then keys/challenges, then tags
```

## 2. Fields and notation

| Symbol | Definition | Where |
|---|---|---|
| **Fp** | P-256 base field, p = 2^256 − 2^224 + 2^192 + 2^96 − 1. The coprocessor's proof field. Wraps `p256::FieldElement`. | `src/field.rs:20` |
| **n** | P-256 group order, n = 0xffffffff00000000ffffffff ffffffffbce6faada7179e84 f3b9cac2fc632551. Not a proof field; mod-n facts are proven with quotient hints. | `src/ecdsa.rs:23` |
| **GF(2^128)** | Binary field with reduction polynomial x^128 + x^7 + x^2 + x + 1 (the Longfellow/GCM-style polynomial). Used only for the cross-proof MAC. | `src/mac.rs` |
| eq(x, y) | Multilinear equality polynomial ∏ᵢ (xᵢyᵢ + (1−xᵢ)(1−yᵢ)) | `src/sumcheck.rs:1222` |
| W̃ | Multilinear extension (MLE) of a value vector over the boolean hypercube | `src/mle.rs` |

Serialization is 32-byte big-endian throughout; the Fiat-Shamir hash is BLAKE2s-256.

## 3. Circuit model

`src/circuit.rs`, `src/gates.rs`.

A circuit is a list of **layers**, output layer first. A layer maps an input vector of
size 2^(next_log_size) to an output vector of size 2^(out_log_size) through a bag of
**quadratic terms**:

```rust
pub struct QuadTerm { out: u32, l: u32, r: u32, coeff: Fp }   // circuit.rs:4
```

with semantics `output[out] += coeff · input[l] · input[r]`. Wiring is explicit
(indices), not algebraic; index bounds are validated at construction
(`circuit.rs:46-69`). Adjacent layers must chain: `layers[i].next_log_size ==
layers[i+1].out_log_size`.

A **witness** is one value vector per layer boundary: `witness[0]` is the output
layer, `witness[L]` is the circuit input. The circuit is **satisfied iff `witness[0]`
is all zeros** and each `witness[i]` equals the layer-i evaluation of `witness[i+1]`
(`circuit.rs:185`). All constraints are therefore written as "this expression must
evaluate to 0", accumulated into output wires.

Linear terms are expressed as quadratic terms against a constant-1 wire; affine curve
formulas fit in degree 2 per layer because inversions are replaced by hint wires (§6).

## 4. GKR sumcheck

`src/sumcheck.rs`. This layer reduces "the output layer is all zeros" to two MLE
evaluation claims about the circuit *input*, which are then discharged against the
Ligero commitment (§5).

### 4.1 The per-layer identity

For a layer with gate set G, the output MLE satisfies, for any point y:

```
W_out(y) = Σ_{zL, zR ∈ {0,1}^d}  Q(y; zL, zR) · W_in(zL) · W_in(zR)

Q(y; zL, zR) = Σ_{(out,l,r,c) ∈ G}  c · eq(y, out) · eq(zL, l) · eq(zR, r)
```

where d = next_log_size. Q is the (sparse) MLE of the wiring; the verifier can
evaluate Q at any point directly from the gate list in O(|G|·d) time — no commitment
to wiring is needed. This is the standard GKR structure with the wiring predicate
made explicit.

### 4.2 Layer reduction, two claims to two claims

The protocol maintains **two** claims per layer boundary — `W(r⁽⁰⁾) = w⁽⁰⁾` and
`W(r⁽¹⁾) = w⁽¹⁾` — because each layer's sumcheck naturally *produces* two claims about
the next layer (one for the left operand, one for the right). Rather than letting
claims multiply, the two incoming claims are folded into one sumcheck instance with a
random blend (`sumcheck.rs:193-196`):

1. Draw α from the channel. Set the initial claim c = α·w⁽⁰⁾ + (1−α)·w⁽¹⁾.
2. Run a sumcheck for the statement

   ```
   c  =  Σ_{zL,zR}  Ψ(zL,zR) · W_in(zL) · W_in(zR),
   Ψ  =  α·Q(r⁽⁰⁾; ·,·) + (1−α)·Q(r⁽¹⁾; ·,·)
   ```

3. The sumcheck runs **2d rounds** (phase A binds zL coordinate by coordinate, phase B
   binds zR). Each round variable appears with **degree ≤ 2** (once through Ψ's eq
   factor, once through the corresponding W_in factor). The prover sends the two
   evaluations [p(0), p(2)]; the verifier derives p(1) = c − p(0) from the current
   claim, checks that consistency, and updates the claim by Lagrange interpolation of
   the degree-2 polynomial at the fresh challenge (`sumcheck.rs:569-580`).

4. After 2d rounds the point s splits into (left, right). The prover sends
   w'_L = W_in(left) and w'_R = W_in(right), and the verifier performs the **layer
   exit check** (`sumcheck.rs:598`):

   ```
   current claim  ==  Ψ(left, right) · w'_L · w'_R
   ```

   with Ψ(left, right) evaluated directly from the gate list. The two new claims
   (W_in(left), W_in(right)) become the next layer's inputs, blended with a fresh α.

At the top, the two initial output-layer claims are evaluations of an all-zero vector,
so they are 0. At the bottom (circuit input), the two surviving claims are emitted as
`InputClaims { points: [Vec<Fp>; 2], values: [Fp; 2] }` (`sumcheck.rs:46`) and handed
to Ligero as linear claims against the committed witness.

### 4.3 Deterministic pads

Every transmitted round value and claim is offset by a pad derived from a **fixed,
public seed** ([0u8;32], domain `eu-id-ec-coproc-otp-pad-pair-v1`, layer/round/kind
indices — `sumcheck.rs:673-680`). The verifier regenerates the pads, unmasks, and
additionally checks the recorded pad triple satisfies padL·padR = padLR
(`sumcheck.rs:442`).

Because the seed is fixed and public, these pads are **transcript-format scaffolding,
not a hiding mechanism**: prover and verifier compute identical pads, masking and
unmasking cancel exactly, and soundness is unaffected. Zero-knowledge in the current
system comes from the Ligero layer (§5.4). If the pads are ever meant to carry ZK
weight, the seed must become private prover randomness with the pads communicated
under commitment — tracked as a hardening item (§10).

### 4.4 Sparse Q evaluation

Prover-side round computation switches between a per-term `prefix_eq` product (sparse)
and a dense eq-table at a 50,000-term threshold (`sumcheck.rs:8`, `:949-961`). This is
a pure performance switch; both paths compute the same values.

## 5. Ligero witness commitment

`src/ligero.rs`, `src/rs.rs`, `src/merkle.rs`. This is the only cryptographic
commitment in the coprocessor; everything upstream reduces to MLE claims checked here.

### 5.1 Commitment

The flat witness is split into rows of ℓ = `row_len` = 64 field elements. Each row is:

1. zero-padded to ℓ, then padded to k = `degree_bound` with **fresh random field
   elements** (OS-RNG-seeded channel, `ligero.rs:638-642`) — this randomness is the
   hiding material;
2. Reed-Solomon encoded: the row is interpreted as evaluations of a degree-<k
   polynomial on the **systematic equispaced domain {0, 1, …} ⊂ Fp** and extended to a
   codeword of length n = `codeword_len` (`rs.rs:42-217`). Rate k/n, distance
   n − k + 1.

Two extra random rows are appended and encoded: a **proximity mask row** (degree < k)
and a **claim blind row** (degree < k + ℓ − 1, drawn uniform and then one slot adjusted
so its systematic-prefix sum is exactly zero — the C-p4b-blind-claim fix, §5.3,
`ligero.rs:195-205`). The n columns of the resulting matrix
are Merkle-committed with BLAKE2s (leaf = full column, domain-separated leaf/node
hashes, `merkle.rs:124-141`). The root is the witness commitment, and it is absorbed
into the Fiat-Shamir channel **before any sumcheck or Ligero challenge is drawn**
(`sumcheck.rs:655-667`).

### 5.2 Proximity test

Establishes that the committed rows are (close to) genuine RS codewords, so a
well-defined witness exists.

- Verifier sends random γ ∈ Fp^(#witness rows).
- Prover responds with the first k coordinates of `mask_row + Σ γᵢ·rowᵢ`
  (`ligero.rs:243-263`) — a claimed degree-<k polynomial.
- Verifier samples t = `openings` distinct column indices. RS sampling excludes
  its separately opened systematic prefix; Circle sampling covers the full
  non-systematic codeword domain. For each opened column j it checks
  the Merkle path and that
  `mask[j] + Σ γᵢ·columnᵢ[j] == (claimed polynomial evaluated at j)`
  (`ligero.rs:644-684`).

By the Ligero proximity argument, if any row is far from the code, a random γ
combination is far from the code with overwhelming probability, and each opened
column then catches the discrepancy independently.

### 5.3 Evaluation (claim batch) argument

Discharges the sumcheck's `InputClaims` plus the public-input **fixed claims** (§6.5).
Each claim is `LigeroLinearClaim { offset, len, point, value }`: an assertion that the
MLE of `witness[offset..offset+len]` at `point` equals `value`. MLE evaluation is a
weighted sum Σ wᵢ·witnessᵢ with weights wᵢ = eq(point, i), so every claim is a linear
functional of the witness.

Batched with fresh γ (`ligero.rs:310-341`, verification `:686-767`):

- For each claim and each row, the weight vector restricted to that row is a function
  on the ℓ systematic domain points, hence a degree-<ℓ polynomial W_row. The prover
  sends the coefficients of

  ```
  q  =  blind_row  +  Σ_claims γ_c · Σ_rows W_row · P_row        (deg < k + ℓ − 1)
  ```

- Per opened column j, the verifier recomputes every W_row(j) itself and checks
  `q(j) == blind[j] + Σ γ_c·Σ W_row(j)·column_row[j]`.
- Final check: because the encoding is systematic on {0,…,ℓ−1},
  Σ_{x=0}^{ℓ−1} W_row(x)·P_row(x) is exactly the weighted witness sum, so

  ```
  Σ_{x<ℓ} q(x)  ==  blind_claim + Σ_c γ_c · value_c      with blind_claim REQUIRED == 0
  ```

  If any claimed value is wrong, the true q′ and the claimed q are distinct
  polynomials of degree < k + ℓ − 1, so they disagree on all but (k + ℓ − 1) of the n
  columns and the t random openings catch it.

**C-p4b-blind-claim (CRITICAL, found 2026-07-06 in the Q-025 review, fixed in-tree).**
The check above only binds anything because `blind_claim` is forced to a public
constant. In the original protocol `blind_claim` was a *prover-sent scalar* whose sole
use was this equation; the column checks bind `q` to blind + Σ γ·W·rows, so q_sum is
honest — but a prover claiming wrong values could simply send
`blind_claim′ = q_sum − Σ γ_c·(fake value_c)` and pass every check. Since γ is drawn
before `blind_claim` is sent, Fiat-Shamir did not prevent it. The claim batch — the
only link between the sumcheck's input claims and the commitment — was vacuous:
commit garbage, run the sumcheck on a fake witness, compensate via `blind_claim`.

The fix (Q-025 prescription, landed in the working tree): at commit time the blind
row is drawn uniform and one slot is adjusted so Σ_{x<ℓ} blind(x) = 0
(`ligero.rs:195-205`); the verifier **requires `blind_claim == 0`** in both
`verify_claim_batch` and `verify_split_claim_batch` (`ligero.rs:496-499`, `:723`);
and a real negative test tampers a claim value *with* the compensating blind_claim
and must reject (`ligero.rs:978-1009`). Hiding is unaffected — the blind row stays
uniform on the sum-zero subspace, and the one functional it no longer masks
(Σ γ·value) is public anyway. The `blind_claim` field survives (pinned to zero) only
until the circle-FFT version bump deletes it (§5.6).

The mdoc P4b integration additionally uses a **split (two-root) row-group variant**
of both the proximity test and the claim batch (Q-024): rows are partitioned into two
groups with separate Merkle roots, and `split_claim_batch` /
`verify_split_claim_batch` span the combined rows with the same algebra and the same
blind-claim rule.

### 5.4 Zero-knowledge

- Random padding of every witness row beyond the data prefix means opened columns of
  witness rows are individually uniform.
- The proximity mask row makes the γ-combination response uniform.
- The claim blind row makes the batched polynomial q uniform subject to the single
  checked sum-zero functional (which reveals only the public value Σ γ·value).

This is the standard Ligero hiding argument; masking is information-theoretic, sourced
from OS randomness independent of the transcript.

### 5.5 Parameters and exact soundness

`ligero.rs:106-116` implements the Ligero soundness bound

```
ε_ligero = (1 − e/n)^t + (2k/n)^t + ((k+ℓ)/n)^t + (n+3)/2^256
```

(proximity miss, degree slack, claim-degree slack, hash term), with `validate()`
enforcing the preconditions (2e < n − (k+ℓ−1), n > 2k + e, k ≥ ℓ + t, …;
`ligero.rs:77-100`).

| Set | ℓ | k | n | t | e | rate | ε |
|---|---|---|---|---|---|---|---|
| v1 (legacy) | 64 | 64 | 512 | 160 | 223 | 1/8 | fails `validate()`; unused |
| **v2a** | 64 | 234 | 2048 | 170 | 875 | 11.4% | **2^−136.7** |
| **v2b** | 64 | 289 | 1024 | 225 | 335 | 28.2% | **2^−128.6** |

Both live parameter sets are gated by tests asserting ε ≤ 2^−128
(`tests/ligero.rs:314,324`).

### 5.6 Circle-FFT encoding front-end (P4b MAC-bundle prove-time lever, Q-025)

**Why.** RS encoding dominates the P4b MAC bundle's prove time: at the current
checkpoint (`9e1ac686`, single-thread release probe) the bundle proves in ~4.45 s of
which **~2.81 s is RS encode** (proof ~5.26 MB, verify ~264 ms). The cause is
structural: the multiplicative group of Fp has 2-adicity 1 (p − 1 = 2·odd), so no
radix-2 multiplicative FFT domain exists and the equispaced-domain encoder must use
O(k·n)-class finite-difference/Lagrange extension. But the **circle group**
C(Fp) = {(x, y) : x² + y² = 1} has order p + 1 = 2^96·(2^160 − 2^128 + 2^96 + 1) —
2-adic subgroups up to 2^96 — so a stwo-style **circle FFT works over Fp** and makes
encoding O(n log n). Projected effect: encode 2.81 s → ~0.10 s, bundle prove
~1.75–1.9 s, under the parity gate.

**Why it is not just an encoder swap.** A naive swap (encode/evaluate through the
circle basis) was tried and correctly rejected: circle-FFT messages are
*coefficients*, not evaluations. The whole claim-batch protocol (§5.3) rests on one
fixed, claim-independent extraction functional — "sum the batch polynomial over the
systematic prefix" — which is what allows the blind row to be committed with that
functional pre-zeroed. In a coefficient-basis code any direct extraction functional
becomes claim-dependent (it moves with the MLE point), and a claim-dependent
functional cannot be pre-zeroed on a blind row committed before the claim points
exist: every such design either leaks or reopens exactly the C-p4b-blind-claim hole.
The conclusion (Q-025): keep the fixed functional and **put the data back into
evaluation positions** — an encoding-front-end change, not a claim-protocol change.

**The design: systematic-by-interpolation.** Fixed public setup (precomputed tables,
`src/circle_fft.rs`):

- **D2048** — codeword domain of size 2048 (points of order 4096), `CIRCLE_CODEWORD_LEN`;
- **D256** — message domain of size 256 (generator of order 512), disjoint from D2048
  by construction (order check asserted), `CIRCLE_ROW_MESSAGE_LEN`;
- **S_data ⊂ D256** — 64 designated data slots (`CIRCLE_DATA_SLOTS`), with the 64×64
  interpolation inverse M64⁻¹ precomputed and asserted invertible.

Per-row commit path: 64 data values into the S_data slots + **192** random pad values
into the remaining D256 slots (pad budget 170 → 192, still ≥ t; same pad-channel
rules) → IFFT₂₅₆ → 256 coefficients → zero-pad → FFT₂₀₄₈ → codeword. Rows are then
evaluation-systematic again: R(s_j) = data_j by construction.

Protocol deltas versus §5.2–5.3:

- **Proximity**: prover sends the combined *coefficients* (length 256); verifier
  checks `circle_evaluate(combined, i)` against the γ-combined opened symbols. No
  codeword-membership check is needed — every coefficient vector is a valid message.
- **Claim batch**: the batch message is the 322 coefficients of
  Q = blind + Σ_r W_r·R_r, where W_r interpolates the γ-batched row weights at S_data
  (w_coeffs_r = M64⁻¹·ω_r, `circle_weight_coeffs`). Per opened column i:
  `circle_evaluate(Q, i) == blind_symbol(i) + Σ_r circle_evaluate(w_coeffs_r, i)·column[r]`.
  The systematic-prefix sum check becomes
  `Σ_{s∈S_data} Q(s) == Σ_c γ_c·value_c` (`circle_data_sum`), with the blind row's
  S_data-sum zeroed at commit time — the `blind_claim` field is **deleted** in this
  version; no prover-supplied scalar remains in the equation.
- **Parameter fork** (validate()/soundness_error() forked for the circle variant):
  k 234 → **256**, claim degree bound **322** (function space F_d = {P(x) + y·Q(x)};
  the y² = 1 − x² fold makes the product bound a + b + 2, not a + b − 1),
  e 875 → **862** (2e < 2048 − 322). Soundness: (1 − 862/2048)^170 ≈ 2^−134,
  (2·256/2048)^170 = 2^−340, (322/2048)^170 ≈ 2^−453 ⇒ **ε ≈ 2^−134**, above the
  2^−132 target. ℓ = 64, t = 170, n = 2048 unchanged, so matrix height, Merkle shape
  and proof-size class are unchanged (batch coefficients 297 → 322, +25 Fp ≈ 800 B,
  minus the deleted field).

**Status.** `src/circle_fft.rs` (638 lines: domains, LOG_N-parametrized fft/ifft,
`circle_encode`, `circle_evaluate`, `circle_encode_row`, `circle_data_sum`,
`circle_weight_coeffs`) is in the tree and exported from `lib.rs`, but the Ligero
encoder swap and the parameter fork are **not yet wired** — sequencing per Q-025 is
blind-claim fix → fixture re-pin → circle integration. Landing gates: basis
round-trip (IFFT₂₅₆ → pad → FFT₂₀₄₈ → `circle_evaluate`) agreeing at random columns
*and* at all 64 S_data points; D256 ∩ D2048 = ∅ assert; M64⁻¹ existence; tail-zero
assert on batch coefficients [322..]; and the compensating-blind-claim forgery
negative re-run on the circle path.

## 6. The ECDSA circuits

`src/ecdsa.rs`. The statement, per signature:

> Given an accepted input (z, r, s, Q = (qx, qy)): Q is on the P-256 curve,
> 0 < r,s < n, u1 = z·s⁻¹ mod n, and u2 = r·s⁻¹ mod n; the constrained point
> R = u1·G + u2·Q satisfies R.x ≡ r (mod n).

The production projection may hide some of these values. “Given” therefore means
verifier-fixed when public and equality-bound inside the commitment when private.
All ECDSA-family constant-one wires are also verifier-fixed Ligero claims; they are
not trusted merely because the prover's input builder writes one.

### 6.1 Witness layout

One 1,135-element native witness vector:

| Slots | Content |
|---|---|
| 0–99 | 20×13-bit limbs of z, r, s, qx, qy |
| 100–101 | u1, u2 |
| 102–1125 | 256 + 256 ladder accumulator points (x, y) for u1·G and u2·Q |
| 1126–1129 | corrected ladder endpoints (inputs to the final add) |
| 1130 | final-add denominator inverse used by C11 |
| 1131–1132 | R = (Rx, Ry) |
| 1133–1134 | final reduction (k, r′) |

The native witness is not committed at shared physical offsets. Each circuit family
builds its own padded input vector, and those vectors are concatenated into one Ligero
commitment. Values used by more than one family are equal only when the verifier adds
an explicit fixed or cross-family affine claim. The current claim batch adds
zero-valued affine equalities for every shared private value; it does not serialize
the values themselves.

### 6.2 Circuit families

| Family | In/out log-size | Enforces |
|---|---|---|
| C1 input-limbs | 7 / 3 | value = Σ limbᵢ·2^(13i) for each of z, r, s, qx, qy |
| C2 canonicality | 2 / 1 | qy² = qx³ − 3·qx + b (Q on curve); C2 is key-only |
| C3–C5 scalar setup | 13 / 13 | exact 13-bit integer range/nonzero checks, z reduction, and limb/carry proofs of s·u1 ≡ z and s·u2 ≡ r (mod n) |
| C9–C10 ladder | 13 / 14 | u1,u2 < n, scalar-bit decomposition, and every double/conditional-add transition for u1·G and u2·Q |
| C11 final add | 4 / 2 | affine addition of the two ladder endpoints via hinted slope: λ = (b_y−a_y)·inv, Rx = λ²−a_x−b_x, Ry = λ(a_x−Rx)−a_y |
| C12 final on-curve | 11 / 11 | on-curve check for all 515 points incl. R |
| C14–C15 final check | 11 / 11 | r < n, Rx < p, k boolean, and exact no-wrap limb/carry equality Rx = r + k·n |

The gate-count regression pins the complete seven-family inventory below 80,000
quadratic terms.

### 6.3 Scalar multiplication

The witness generator computes a 256-step MSB-first double-and-add ladder for u1·G
and u2·Q. C9/C10 range-checks each scalar below n, constrains its bits, proves every
doubling and selected mixed addition, and binds both final endpoints. Cross-family
affine claims tie C3's u1/u2 to C9, C9 to C11/C12, and C11 to C12/C14. C12
independently checks every supplied affine point is on P-256.

### 6.4 Nondeterministic hints and their pinning

The currently constrained hints are:

| Hint | Pinned by |
|---|---|
| C3 reduction quotients/carries | range-constrained 13-bit integer multiplication and carry equations |
| u1, u2 | exact C3 integer relations with r,s,u1,u2 < n and r,s nonzero |
| ladder inverses/slopes/points | C9/C10 denominator, curve-transition, bit-selection, and endpoint equations |
| final-add inverse | C11 enforces (b_x−a_x)·inv = 1 |
| R, k, r′ | C11 addition formula, C12 on-curve, and exact C14 integer reduction |

The C3 and C14 equations are integer limb/carry relations, not equations with an
unrestricted quotient in Fp. This distinction prevents a prover from satisfying a
purported mod-n equation merely by dividing by n in the base field, and prevents
the former Rx = r+n−p wraparound witness.

### 6.5 Public inputs

`EcdsaPublicProjection` selects which of {z, r, s, qx, qy} are
public for a given instance. Each public field is bound by **fixed Ligero claims**:
the verifier computes, from the actual public bytes, the expected MLE evaluations of
the corresponding witness slots, and adds those claims to the batch (§5.3) itself.
The prover cannot influence them. Bindings are added per family that consumes the
value (C1, C2, C3, C9, and C14), all against the same commitment.

For projected-out values, the verifier constructs deterministic zero-valued affine
claims between every family copy. Issuer z and device Q are additionally bound to
the outer proof through the MAC in §7. The proof-format compatibility field
`consistency_claim_values` is always empty and verifiers reject a non-empty legacy
inventory, so no private equality witness is exposed in serialized proofs.

### 6.6 Accepted-input and exceptional-trace boundary

The proof now enforces r,s < n, nonzero r,s, scalar arithmetic, ladder transitions,
and final no-wrap reduction. Input construction still requires z,qx,qy to be
canonical base-field encodings (<p). Exceptional affine traces whose intermediate
point is infinity have no witness in the current ladder representation. These are
completeness restrictions, not alternate accepting witnesses; §10 records the
remaining standards-coverage work.

## 7. Cross-proof binding: the GF(2^128) MAC (P4b)

`src/mac.rs`, `crates/eu-id-prover/src/mdoc_mac.rs`, `mdoc.rs`.

### 7.1 What must be bound

In the mdoc integration the coprocessor proves two ECDSA verifications (issuer
signature over the MSO, device signature over the session transcript). Values shared
with the outer M31 proof split in two classes:

- **Public on both sides** (issuer public key from x5chain, device message hash
  derived from the verifier's nonce): exposed directly through the P4b public
  projection (`issuer_key_only`, `message_hash_only`) and mixed by the outer verifier
  — plain public-input equality, no MAC needed.
- **Witness on the outer side** (issuer message hash z = SHA-256 of the MSO, computed
  inside the outer AIR; device public key Q_device, extracted from the MSO in the
  outer AIR): these are private, so equality must be proven without revealing them.
  Six 128-bit halves are bound: z_issuer (lo, hi), Qx_device (lo, hi),
  Qy_device (lo, hi).

### 7.2 Construction

For each bound half x ∈ GF(2^128):

```
tag = (a_p ⊕ a_v) · x        in GF(2^128), poly x^128 + x^7 + x^2 + x + 1
```

(`mac.rs:8-10`), with the key split into two shares fixed at different transcript
stages:

- **a_p**: sampled fresh per proof from OS randomness (6 independent shares,
  `mdoc.rs:3125-3130`) and committed *inside the coprocessor bundle* as witness.
- **a_v**: derived by Fiat-Shamir from the transcript seed and the coprocessor
  bundle's Merkle root, `a_v = H(seed, bundle.root)` (`mdoc_mac.rs:884-898`,
  `lib.rs:445-450`) — i.e. fixed only **after** both x and a_p are committed.

Both proofs compute the same tag from their own copy of x:

- the **coprocessor** MAC circuit computes (a_p ⊕ a_v)·x over its committed witness
  halves and exposes the 6 tags in the bundle;
- the **outer M31 AIR** (`mdoc_mac.rs`: consumer component lines 403-559, binding
  component 561-629) recomputes the tag bit-serially — a Horner/shift ladder over the
  bits of x taken from the outer witness bytes (via the shared logup relations that
  already carry the SHA output and MSO key bytes) — and constrains the final
  accumulator to equal the published tag.

The published (a_v, tags) are mixed into the outer Fiat-Shamir channel before
downstream challenges (`mdoc_mac.rs:320-331`), so they are non-malleable after the
fact.

The coprocessor also reconstructs each 256-bit issuer-z/device-coordinate value
from its low/high MAC halves and proves that integer is below p. The affine claim
to the ECDSA family therefore binds the exact byte value, not merely the same Fp
residue; encodings such as x+p cannot alias the ECDSA field cell.

### 7.3 Why the MAC binds

Suppose the coprocessor's value x and the outer proof's value x′ differ. Both proofs
are sound individually (per §5, §9, and the outer STARK's own soundness), so each
side's tag genuinely equals key·x resp. key·x′ with key = a_p ⊕ a_v. Equal tags then
force key·(x ⊕ x′) = 0; since GF(2^128) is a field and x ⊕ x′ ≠ 0, this requires
**key = 0**, i.e. a_p = a_v.

The prover chooses a_p, but a_p is committed (inside the bundle whose root feeds the
derivation) *before* a_v = H(seed, root) is known. Hitting a_p = a_v therefore
requires predicting a 128-bit hash output: probability 2^−128 per attempt, subject
only to grinding on the bundle (each grind attempt is a full recommit). For key ≠ 0
the map x ↦ key·x is a bijection, so tag equality implies value equality
**unconditionally** — the 2^−128 is the entire binding error, not a per-forgery
budget that degrades with usage.

Mix-and-match across the six halves fails for the same reason: the six a_p shares are
independent, and swapping value/tag pairs between slots changes which (key, x) pair
must collide.

Without this binding the two proofs would be about unrelated values: a prover could
present a coprocessor proof for one credential's issuer signature while the outer
proof discloses attributes of another (credential substitution), or bind the device
signature to a different device key. The SDK-level variant of exactly this class of
bug (predicate bypass) was found and fixed on `fix/mdoc-sdk-predicate-binding`.

## 8. Fiat-Shamir transcript

`src/channel.rs`. Single BLAKE2s-256 sponge-style channel:

- **Absorb**: every input is length-prefixed (`mix_bytes` writes len ‖ bytes), field
  elements as 32-byte BE. Domain separation at initialization (seed ‖ domain string)
  and per-protocol (`eu-id-ec-coproc-sumcheck-v1`, Ligero leaf/node/pad domains).
- **Squeeze**: `draw_fp` clones the state, appends a monotonically increasing counter,
  finalizes, and reduces the 256-bit digest mod p. Counter guarantees distinct
  challenges without re-absorption.

Ordering, which is what soundness needs:

1. circuit shape + **Ligero Merkle root** absorbed (`mix_circuit_domain`);
2. per sumcheck round: prover message absorbed → challenge drawn;
3. per layer: masked next-claims absorbed → next α drawn;
4. Ligero γ (proximity, then claim batch) and the t opening indices drawn after all
   claims are absorbed;
5. in the mdoc integration: bundle root → a_v derivation → tags absorbed into the
   *outer* channel before outer challenges continue.

Every challenge is derived after the message it must be independent of. One
sampling note: reducing a uniform 256-bit string mod p leaves a statistical bias of
order 2^−32 toward small residues (p ≈ 2^256 − 2^224), but every field element still
has probability ≤ 2·2^−256, so Schwartz–Zippel-type error bounds degrade by at most a
factor 2 — irrelevant at these margins.

## 9. Soundness: composition and budget

The end-to-end argument, stated as a chain — each step conditions on the previous:

1. **Commitment binding.** The Merkle root fixes one matrix of columns
   (BLAKE2s-256 collision resistance, ≈ 2^−128).
2. **Proximity.** If the committed rows are not within the proximity radius of the RS
   code, the γ-combination test fails except with the (1−e/n)^t term of ε_ligero.
   Within the radius, each row decodes uniquely → a **well-defined witness vector**
   exists.
3. **Evaluation correctness.** Any false `LigeroLinearClaim` (sumcheck input claim or
   verifier-computed fixed claim) survives the claim batch with probability bounded by
   the remaining ε_ligero terms (distinct low-degree polynomials agree on few
   columns) plus 1/p for the γ batching collision. This step **requires the
   verifier-enforced `blind_claim == 0`** together with the commit-time sum-zero
   blind row — without it the step is void (C-p4b-blind-claim, §5.3).
4. **Sumcheck.** Given correct input-layer MLE evaluations, a false "output layer is
   zero" claim survives layer-by-layer with probability ≤ Σᵢ (2·2dᵢ + O(1))/p
   ≈ 2^−240s — Schwartz–Zippel over degree-2 round polynomials plus the α-blend and
   the two initial random points. So the committed inputs satisfy all seven
   implemented circuit families.
5. **Arithmetization boundary.** Exact C3 integer arithmetic derives u1/u2 from
   z,r,s modulo n; C9/C10 constrains the complete scalar-selected ladders; C11/C12
   constrain the final point; and exact C14 reduction binds R.x to r. Fixed and
   zero-valued affine claims make these one relation even when the production
   projection hides r and s.
6. **Cross-proof binding.** The MAC (§7.3) forces the coprocessor's z_issuer and
   Q_device to equal the outer proof's committed values except with ≈ 2^−128;
   directly-projected public values are checked by equality.
7. **Fiat-Shamir.** The interactive-to-non-interactive step is sound in the random
   oracle model for BLAKE2s-256, with all commit-before-challenge orderings respected
   (§8); the FS security loss is the usual q_H multiplicative factor on the above.

Budget summary (per proved bundle, dominant terms):

| Source | Error |
|---|---|
| Ligero (production v4 Circle, full-domain sampling) | ≈ 2^−132.16 |
| Merkle / channel collisions (BLAKE2s-256) | ≈ 2^−128 |
| MAC binding (per proof, incl. grinding resistance) | ≈ 2^−128 |
| GKR sumcheck (all layers, all families) | ≲ 2^−240 |
| γ batching, α blends, sampling bias | ≲ 2^−250 |
| **Total for the implemented algebraic relation** | **≈ 2^−127 (union bound)** |

The 2026-07-23 coprocessor audit (`/Users/lucas/stwo/tasks/coprocessor-audit.md`)
supersedes the older relation analysis. It found four release blockers: unbound
hidden family copies, vacuous Fp “mod-n” equations, missing scalar/no-wrap integer
semantics, and serialized private consistency values. The current v2 circuit and
claim shape closes those four findings. The numeric table above remains a backend
error budget; the residual privacy/accounting assumptions listed in §10 still need
their own reviewed bounds.

## 10. Residual gaps and hardening items

The four 2026-07-23 release blockers are closed in the v2 relation:

1. every hidden ECDSA family copy is connected by verifier-constructed affine
   equality claims;
2. C3 scalar arithmetic and C14 final reduction are exact bounded integer
   relations;
3. r,s,u1,u2 and R.x have the required n/p bounds and no-wrap semantics; and
4. private consistency values are not serialized.

The audit also records the following non-release-blocking work. These items must not
be described as already solved:

1. **Biased Fp draws (medium privacy/protocol ambiguity).** Digest reduction gives
   roughly 2^-32 statistical distance from uniform for Ligero masks. Rejection
   sampling or a published accumulated hiding bound is still required.
2. **Security accounting (medium).** `soundness_error()` reports algebraic terms as
   though BLAKE2s binding were statistical. The commitment assumption should be
   documented separately in the approximately 128-bit collision-resistance class.
3. **Circle hiding theorem (medium privacy assurance).** Current dimensions exceed
   the maximum opening count, but the joint full-rank property for every supported
   opening set is not yet pinned by a theorem and executable rank gate.
4. **Dense-sumcheck cancellation (correctness).** A zero-as-unseen sentinel can
   duplicate a right index after coefficient cancellation and reject an honest
   proof. This is a completeness bug, not an accepting-proof path.
5. **Transcript/circuit-shape hardening.** Semantic labels were bumped to v2 for
   this repair, but the transcript still does not absorb a canonical digest of all
   circuit wiring and coefficients.
6. **Malformed Circle geometry (availability).** Invalid public geometry can panic
   while holding a global cache mutex. Production presets are valid, but the type
   should make invalid geometry unrepresentable.
7. **Low assurance gaps.** Merkle path shape validation, an independent field
   reduction oracle, the documented Circle distance boundary, and a production
   projection transcript KAT remain desirable.
8. **Low-level verifier API.** `verify_implemented_circuit_proofs` verifies
   per-family sumchecks and deliberately returns unbound input claims. It is
   documented as non-production; accepting a statement requires the bundle
   verifier, which authenticates those claims and adds all family bindings.

Two accepted-input completeness restrictions are also explicit:

- z is currently required to be a canonical Fp encoding. Standard P-256 permits
  every 256-bit digest, so the rare z >= p case needs an exact-byte binding design
  that does not rely on an Fp value cell.
- the affine ladder representation does not encode the point at infinity; valid
  scalar setups such as u1=0 can therefore be rejected as exceptional traces.

Finally, the serialized `consistency_claim_values` field remains only for wire-format
compatibility. Provers emit it empty and verifiers reject non-empty values; delete it
at the next deliberate proof-format break.

## 11. File map

| Path | Contents |
|---|---|
| `src/field.rs` | Fp wrapper over `p256::FieldElement`, batch inversion |
| `src/channel.rs` | BLAKE2s-256 Fiat-Shamir channel (length-prefixed absorb, counter squeeze) |
| `src/circuit.rs`, `src/gates.rs` | layered circuit, `QuadTerm` gates, witness evaluation |
| `src/mle.rs` | multilinear extension, O(2^n) fold evaluation |
| `src/sumcheck.rs` | GKR layer reduction, two-claim α-blend, degree-2 rounds, pads |
| `src/rs.rs` | systematic equispaced Reed-Solomon encoder (finite-difference), cached per (k, n) |
| `src/circle_fft.rs` | circle-FFT encoder over Fp (D2048/D256/S_data, systematic-by-interpolation; not yet wired into Ligero — §5.6) |
| `src/merkle.rs` | column-leaf BLAKE2s Merkle tree |
| `src/ligero.rs` | commitment, proximity test, claim batch, parameters + `soundness_error()` |
| `src/ecdsa.rs` | witness layout, circuit families C1–C15, public projections, GF(2^128) halves |
| `src/mac.rs` | GF(2^128) multiply and `gf128_tag` |
| `crates/eu-id-prover/src/mdoc_mac.rs` | M31-side MAC consumer + binding AIR components, a_v derivation, tag mixing |
| `crates/eu-id-prover/src/mdoc.rs` | P4b orchestration: key shares, MAC values, binding prover/verifier, projection mixing |
| `tests/` | per-layer tests incl. ε ≤ 2^−128 parameter gates, tamper-rejection, determinism |
