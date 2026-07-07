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
- Verifier samples t = `openings` column indices; for each opened column j it checks
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

> Given public (z, r, s, Q = (qx, qy)): Q is on the P-256 curve, r, s ≠ 0,
> and with u1 = z·s⁻¹ mod n, u2 = r·s⁻¹ mod n, the point R = u1·G + u2·Q satisfies
> R ≠ ∞ and R.x ≡ r (mod n).

This is standard ECDSA verification. Working over Fp makes all *curve* arithmetic
native; the two non-native ingredients are mod-n arithmetic (handled with quotient
hints) and division (handled with inverse hints).

### 6.1 Witness layout

One 2680-element Fp vector (`ecdsa.rs:174-193`):

| Slots | Content |
|---|---|
| 0–99 | 20×13-bit limbs of z, r, s, qx, qy |
| 100–105 | s⁻¹ mod n; u1, u2; quotients q_inv, q1, q2 |
| 106–617 | 512 scalar bits (u1 then u2, boolean-constrained) |
| 618–1641 | 256 + 256 ladder accumulator points (x, y) for u1·G and u2·Q |
| 1642–1645 | corrected ladder endpoints (inputs to the final add) |
| 1646–2672 | 1027 slope-denominator inverses (512 + 512 ladder, 1 final add) |
| 2673–2676 | R = (Rx, Ry); final reduction (k, r′) |
| 2677–2679 | infinity flags (native-check only — see §10) |

The whole vector is committed **once** under one Ligero commitment. Nine single-layer
circuit families each run their own sumcheck against sub-ranges of it; because every
family's claims are evaluated against the *same* commitment at fixed offsets, any
value shared between families (u1, u2, accumulator points, R, …) is literally the same
committed element — cross-family consistency needs no extra argument.

### 6.2 Circuit families

| Family | In/out log-size | Enforces |
|---|---|---|
| C1 input-limbs | 7 / 3 | value = Σ limbᵢ·2^(13i) for each of z, r, s, qx, qy |
| C2 canonicality | 3 / 2 | r·r⁻¹ = 1, s·s⁻¹ = 1 (nonzero); qy² = qx³ + 3·qx + b (Q on curve) |
| C3–C5 scalar setup | 4 / 2 | s·s⁻¹ = 1 + q_inv·n; z·s⁻¹ = u1 + q1·n; r·s⁻¹ = u2 + q2·n |
| C6 scalar bits | 10 / 10 | bitᵢ² = bitᵢ for all 512 bits; Σ bits·2^i recomposes u1, u2 |
| C9–C10 ladder on-curve | 11 / 10 | y² = x³ + 3x + b for all 512 accumulator points |
| C11 final add | 4 / 2 | affine addition of the two ladder endpoints via hinted slope: λ = (b_y−a_y)·inv, Rx = λ²−a_x−b_x, Ry = λ(a_x−Rx)−a_y |
| C12 final on-curve | 11 / 11 | on-curve check for all 515 points incl. R |
| C13 slope inverses | 12 / 11 | denomᵢ·invᵢ = 1 for all 1027 hinted inverses |
| C14–C15 final check | 3 / 3 | k² = k; Rx = k·n + r′; r′ = r |

Total ≈ 35k quadratic gates.

### 6.3 Scalar multiplication

Both u1·G and u2·Q use a 256-step MSB-first double-and-add ladder. The prover supplies
every intermediate affine point as witness; the circuits then pin the trace:

- each intermediate point is proven on-curve (C9/C10/C12);
- each doubling/addition step's slope denominator (2y for doubling, Δx for addition)
  has a proven inverse (C13), which both certifies the affine formula and certifies
  **the denominator is nonzero** — excluding the exceptional cases (doubling a
  2-torsion point, adding equal-x points) at every step;
- the step formulas themselves (λ, x', y' relations) are quadratic gates over
  consecutive accumulator slots;
- the bits driving the conditional adds are the C6-boolean bits that provably
  recompose u1 and u2, which are in turn pinned to (z, r, s) by C3.

### 6.4 Nondeterministic hints and their pinning

Every prover-supplied hint has an in-circuit constraint that makes it unique (or
harmless):

| Hint | Pinned by |
|---|---|
| s⁻¹ | s·s⁻¹ ≡ 1 (mod n form with quotient) — unique since s ≠ 0 |
| u1, u2, q1, q2, q_inv | the three mod-n identities in C3 (see §6.6 on ranges) |
| 512 scalar bits | booleanity + recomposition to u1, u2 |
| ladder points | on-curve + step formulas + slope-inverse existence |
| 1027 slope inverses | denom·inv = 1 (unique; also proves denom ≠ 0) |
| R, k, r′ | C11 addition formula, C12 on-curve, C14: Rx = k·n + r′, k boolean, r′ = r |

The mod-n reduction of R.x deserves a note: Rx ∈ Fp, and C14 asserts Rx = k·n + r′
with k ∈ {0,1} and r′ = r. Since r is a valid scalar (r < n, enforced at parse time
and bound as public input) and p < 2n, the decomposition Rx = k·n + r with k ∈ {0,1}
is exactly the statement Rx ≡ r (mod n) with the canonical representative — no larger
k is possible.

### 6.5 Public inputs

`EcdsaPublicProjection` (`ecdsa.rs:2749+`) selects which of {z, r, s, qx, qy} are
public for a given instance. Each public field is bound by **fixed Ligero claims**:
the verifier computes, from the actual public bytes, the expected MLE evaluations of
the corresponding witness slots, and adds those claims to the batch (§5.3) itself.
The prover cannot influence them. Bindings are added per family that consumes the
value (C1 limbs, C2, C3, C14 — `ecdsa.rs:2860-2947`), all against the same
commitment.

This also resolves limb range-checking for public values: the verifier derives the
claims from canonical 13-bit limbs of the true bytes, so non-canonical limb
decompositions simply fail the fixed claims. (For fields that are *projected out* and
bound by MAC instead, see §7 and the gap list in §10.)

### 6.6 What is checked natively rather than in-circuit

Witness generation (`generate_witness`, `verify_witness`) enforces some conditions
with plain Rust asserts that have **no circuit counterpart**:

- r < n and s < n (parse via `Scalar::from_repr`);
- no ladder intermediate and no final R is the point at infinity
  (`is_identity()` checks);
- the three infinity flag slots are zero.

These run on the prover only. Their soundness status is analyzed in §10.

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
   the two initial random points. So the committed witness **satisfies all nine
   circuit families**.
5. **Arithmetization.** A satisfying witness with the public inputs pinned by fixed
   claims is, by §6's constraint inventory, a valid ECDSA verification trace:
   Q on-curve, u1/u2 correctly derived, ladder correct at every step with all
   exceptional cases excluded by the inverse hints, R correctly assembled, and
   R.x ≡ r (mod n). (Residual caveats: §10.)
6. **Cross-proof binding.** The MAC (§7.3) forces the coprocessor's z_issuer and
   Q_device to equal the outer proof's committed values except with ≈ 2^−128;
   directly-projected public values are checked by equality.
7. **Fiat-Shamir.** The interactive-to-non-interactive step is sound in the random
   oracle model for BLAKE2s-256, with all commit-before-challenge orderings respected
   (§8); the FS security loss is the usual q_H multiplicative factor on the above.

Budget summary (per proved bundle, dominant terms):

| Source | Error |
|---|---|
| Ligero (v2b / v2a) | 2^−128.6 / 2^−136.7 |
| Merkle / channel collisions (BLAKE2s-256) | ≈ 2^−128 |
| MAC binding (per proof, incl. grinding resistance) | ≈ 2^−128 |
| GKR sumcheck (all layers, all families) | ≲ 2^−240 |
| γ batching, α blends, sampling bias | ≲ 2^−250 |
| **Total** | **≈ 2^−127 (union bound), i.e. ~128-bit soundness** |

The 2026-07-05/06 backend audit (`tasks/audits/2026-07-05-backend-soundness.md`)
reviewed the coprocessor, the γ-digest sharing, and this Ligero accounting at
e9e3c007 and found no confirmed breaks; the "2^−132 exact" figure there corresponds
to the v2 parameter regime above. One day later the Q-025 design review found the
C-p4b-blind-claim hole (§5.3) that the audit's negative tests had missed — they
tampered claim values without compensating the blind scalar. The hole is fixed in
the working tree; the episode is a concrete reminder that this table measures the
protocol *as specified*, and that negative tests must model an adversary who uses
every prover-chosen message. The planned circle-FFT parameter fork lands at
ε ≈ 2^−134 (§5.6), keeping the same overall class.

## 10. Residual gaps and hardening items

**Recently closed:** C-p4b-blind-claim (CRITICAL, prover-chosen `blind_claim` made
the claim batch vacuous — full coprocessor binding bypass) is fixed in the working
tree: sum-zero blind row, verifier-enforced `blind_claim == 0` in both batch
verifiers, compensating-forgery negative test. Details in §5.3. Follow-through items:
the fix changes proof bytes (fixture re-pin required), and the now-redundant
`blind_claim` field is deleted only at the circle-FFT version bump (§5.6) — until
then any new verifier path must remember to enforce the zero check.

Honest inventory of what is *not* enforced in-circuit today. None is a confirmed
break, but each is a place where soundness currently leans on something outside the
proof.

1. **r, s < n is prover-side only.** The circuit binds r and s as Fp values
   (< p) via fixed claims from the public bytes; the verifier-side byte parsing is
   what rejects r, s ≥ n. Safe **as long as every verifier path parses the signature
   through `parse_nonzero_scalar` / `Scalar::from_repr` before building fixed
   claims** — that parsing is part of the trusted verifier code, not the proof.
   Hardening: an in-circuit < n comparison, or an explicit verifier-side contract
   test.

2. **Point-at-infinity handling is native-only.** `is_identity()` rejections for
   ladder intermediates and R, and the three `InfinityFlags` witness slots, are
   checked by prover-side code, not constraints. Mitigating structure: every ladder
   step's slope-denominator inverse (C13) already proves the affine formulas were
   never degenerate, and C12 proves R on-curve with a definite (Rx, Ry) — an "R = ∞"
   trace has no consistent affine representation that satisfies C11 + C12 + C13.
   The flags themselves are dead weight in-circuit. Hardening: constrain the flags to
   zero (3 gates) or delete the slots, and write down the no-affine-representation
   argument as a test.

3. **Limb ranges for MAC-bound (non-public-projected) values.** For fields bound via
   fixed claims, non-canonical limbs are excluded by the verifier-computed claims
   (§6.5). For fields whose binding is the MAC path, the equality is at the level of
   the reconstructed 128-bit halves; the canonical-limb argument should be re-checked
   per projection configuration. Hardening: a per-configuration audit that every
   consumed input field is bound by *either* a fixed claim *or* a MAC half, with
   limbs canonical in both cases.

4. **Sumcheck pads use a fixed public seed** (§4.3). Fine for soundness, contributes
   nothing to ZK. Either document them as structural or upgrade to private-coin
   masks.

5. **a_p commitment timing.** a_p is committed inside the bundle before a_v is
   derived, which the binding argument needs; this ordering is currently implicit in
   the call structure (`prove_mdoc_p4b_circuit_bundle_*` → root → a_v). Hardening:
   an explicit early `H(a_p)` absorb, making the ordering visible in the transcript
   rather than in control flow.

6. **v1 Ligero parameters** fail `validate()` and are legacy; ensure no code path can
   select them (currently only v2a/v2b are constructed).

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
