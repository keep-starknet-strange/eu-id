# EC coprocessor design and security boundary

## Status

This document describes the active EC coprocessor on `build/release-lto`.
The code in `crates/eu-id-ec-coprocessor` is the authority for protocol
details.

The coprocessor proves P-256 ECDSA relations outside the M31 STARK. It uses
layered arithmetic circuits, GKR sumcheck, and a Ligero commitment with Circle
FFT encoding.

## Purpose

P-256 arithmetic in an M31 AIR needs many small limbs and trace columns. The
coprocessor works in the P-256 base field. One field multiplication then uses
one quadratic gate.

The outer proof and coprocessor share some logical values. A GF(2^128) MAC
binds the private copies. Direct public-input checks bind public copies.

The proof flow is:

```text
outer M31 STARK              EC coprocessor
SHA and mdoc values          P-256 ECDSA circuits
MAC consumer AIR     <---->  GKR and Ligero proof
```

Both sides commit their witness data before they derive the MAC key challenge.

## Fields and encoding

| Symbol | Meaning |
|---|---|
| `Fp` | P-256 base field with modulus `2^256 - 2^224 + 2^192 + 2^96 - 1` |
| `n` | P-256 group order |
| `GF(2^128)` | Binary field with polynomial `x^128 + x^7 + x^2 + x + 1` |

Field and scalar byte strings use 32-byte big-endian encoding. The
Fiat-Shamir channel uses BLAKE2s-256.

Modulo-`n` equations use bounded integer limbs and quotient traces. They do
not use an unrestricted quotient in `Fp`.

## Circuit model

A circuit contains output-first layers. Each layer contains quadratic terms:

```text
output[out] += coefficient * input[left] * input[right]
```

`src/circuit.rs` checks all indexes and adjacent layer sizes. A witness has one
vector at each layer boundary.

The output vector must contain only zeros. Constant-one wires express linear
terms as quadratic terms. Hint wires hold inverses and intermediate points.
Other equations constrain every accepted hint.

## ECDSA statement

For an input `(z, r, s, Q)`, the circuits enforce:

```text
0 < r < n
0 < s < n
Q is on the P-256 curve
u1 = z * s^-1 mod n
u2 = r * s^-1 mod n
R = u1 * G + u2 * Q
R.x = r mod n
```

The final equality uses exact integer limbs and a no-wrap reduction. This rule
prevents a base-field alias from satisfying the scalar-field statement.

## Witness layout

One ECDSA witness has 1,135 native field slots:

| Slots | Content |
|---|---|
| 0–99 | 13-bit limbs for `z`, `r`, `s`, `qx`, and `qy` |
| 100–101 | `u1` and `u2` |
| 102–1125 | ladder accumulator points |
| 1126–1129 | corrected ladder endpoints |
| 1130 | final-add denominator inverse |
| 1131–1132 | final point `R` |
| 1133–1134 | final reduction values |

Each circuit family gets a padded input vector. Ligero commits the combined
vectors. Fixed and affine claims bind copies that occur in more than one
family.

## Circuit families

The implementation has seven circuit families:

| Family | Relation |
|---|---|
| C1 | Reconstruct five values from 20 13-bit limbs |
| C2 | Check that `Q` is on the P-256 curve |
| C3–C5 | Check scalar bounds, nonzero values, digest reduction, and `u1`, `u2` |
| C9–C10 | Check both 256-step scalar ladders |
| C11 | Add the two ladder endpoints |
| C12 | Check all supplied affine points on the curve |
| C14–C15 | Check `r`, `R.x`, the reduction bit, and exact no-wrap equality |

C3 and C14 use integer carry equations. C9 and C10 check scalar bits,
transitions, and endpoints. C11 constrains its inverse and affine formulas.

The gate-count regression test pins the builder-call inventory and requires
the structured construction to remove at least 25 percent of the dense terms.

## Scalar multiplication

The witness generator uses a 256-step, most-significant-bit-first ladder. It
computes `u1 * G` and `u2 * Q`.

C9 and C10 constrain each scalar bit and each point transition. C12 checks the
curve equation for the accumulator points. Cross-family affine claims bind
the endpoints to C11.

The affine representation has no point-at-infinity value. The input builder
requires nonzero ladder scalars. This is a completeness limit.

## GKR sumcheck

For one layer, GKR reduces an output MLE claim to two input MLE claims. The
wire polynomial comes directly from the sparse gate list.

The verifier keeps two claims at each boundary. A random coefficient combines
them into one sumcheck. A layer with input log size `d` uses `2d` rounds.

Each round polynomial has degree at most two. The prover sends its values at
zero and two. The verifier derives the value at one from the current claim.

After the rounds, the verifier evaluates the sparse wire polynomial. It checks
the layer exit equation and creates two claims for the next layer.

The final input claims go to Ligero. Public deterministic sumcheck pads define
the transcript format. They do not hide witness values.

## Active Ligero commitment

The production path uses `v4_circle_params()`:

| Parameter | Value |
|---|---:|
| Data values per row | 256 |
| Row message length | 512 |
| Codeword length | 4096 |
| Product domain length | 2048 |
| Open columns | 196 |
| Proximity radius | 1534 |
| Linear-claim degree bound | 770 |
| Quadratic degree bound | 1026 |

Each row has 256 data values and 256 fresh random pad values. Circle FFT
encoding extends the 512-value message to 4,096 symbols.

The prover commits matrix columns in a BLAKE2s Merkle tree. The transcript
absorbs the root before it draws sumcheck or Ligero challenges.

The mdoc bundle uses a split commitment with two roots. The verifier derives
one authenticated root from both parts and checks openings against both trees.

## Ligero checks

The proximity check combines committed rows with a random coefficient. Random
column openings test the result against the Circle code.

The linear-claim batch checks the GKR input claims, public fixed claims, and
cross-family affine claims. A committed blind row hides the batch response.
The verifier checks its zero-sum condition.

The quadratic batch checks committed multiplication relations. Its quotient
uses the polynomial that vanishes on all data slots.

`LigeroParams::validate()` checks the code distance, opening count, degree
bounds, and proximity radius. `validate_quadratic()` also checks the product
domain.

## Ligero soundness bound

The implementation calculates:

```text
epsilon =
    (1 - e/n)^t
  + (2k/n)^t
  + 2 * (linear_bound/n)^t
  + (quadratic_bound/n)^t
  + 2 * (n + 4) / 2^256
```

The production parameter test requires `epsilon <= 2^-132`. The proximity
term is the largest algebraic term.

BLAKE2s commitment binding is a computational assumption. Its collision
security is in the 128-bit class. It is not part of the statistical Ligero
formula.

## Public projections

`EcdsaPublicProjection` can fix any of `z`, `r`, `s`, `qx`, and `qy`. The
verifier calculates fixed Ligero claims from each selected byte string.

Hidden family copies use verifier-defined zero-value affine claims, so no
private equality operands are serialized in the proof bundle.

The production mdoc verifier authenticates all family input claims. The
lower-level family verifier returns unbound input claims and is not a complete
application verifier.

## Cross-proof MAC

The mdoc composition binds eight 128-bit halves:

- two halves of the issuer message digest
- two halves of the mandatory revocation digest
- four halves of the device public-key coordinates

For each half `x`, both proof systems constrain:

```text
tag = a_p XOR (a_v * x)
```

The multiplication and XOR occur in `GF(2^128)`. The prover samples the
additive pad `a_p` from the operating system random source and commits both
`a_p` and `x` in the coprocessor bundle. Fiat-Shamir derives `a_v` only after
that commitment.

The coprocessor circuit calculates the tag from its committed copy. The outer
M31 AIR calculates the same tag from SHA and mdoc witness bytes.

If the committed copies differ by `delta_x`, while their pads differ by
`delta_a_p`, equal tags require the unique challenge
`a_v = delta_a_p / delta_x`. That challenge occurs with probability
approximately `2^-128` for one attempt in the random-oracle model. A zero
value still has the fresh tag `a_p`; it does not use an all-zero special case.

Canonicality constraints require each reconstructed device-key coordinate to
be below the P-256 base modulus. This rule prevents an `x + p` alias. Issuer
and revocation digests instead accept the complete 256-bit SHA-256 output
space and bind its two exact 128-bit halves.

## Transcript order

The channel prefixes each absorbed value with its length. Domain labels
separate circuit, sumcheck, Ligero, and MAC messages.

The protocol uses this order:

1. Absorb the circuit shape and Merkle roots.
2. Absorb each sumcheck message before its challenge.
3. Absorb all claims before Ligero batch challenges.
4. Draw opening indexes after the proof responses.
5. Derive `a_v` after the MAC pad-and-value commitment.
6. Absorb MAC tags before later outer-proof challenges.

Each challenge follows the message that it checks.

## Privacy boundary

Random row pads, proximity masks, claim blinds, and quadratic masks hide the
Ligero commitment openings. Operating system randomness supplies these masks.

This hiding argument applies to the coprocessor commitment. It does not give
proof-wide zero knowledge. The outer M31 proof is transparent.

The current composed proof does not guarantee confidentiality or
unlinkability for logical witness values. Documentation and APIs must not
describe a hidden projection as a privacy guarantee.

## Accepted-input limits

The circuit accepts every 256-bit SHA-256 digest from zero through
`2^256 - 1`. It binds the exact digest limbs and bits, then reduces the integer
modulo the P-256 group order for the ECDSA scalar calculation. It does not
interpret the digest as a P-256 base-field element, so values at or above the
base-field modulus remain valid inputs.

The affine ladder cannot represent an intermediate point at infinity. It can
reject a valid exceptional scalar trace. These cases are completeness limits,
not alternate accepted witnesses.

## Verification

Run the standard coprocessor tests:

```bash
cargo test -p eu-id-ec-coprocessor
```

Run the ignored production bundle tests in release mode:

```bash
cargo test --release -p eu-id-ec-coprocessor \
  --test ecdsa_circuit -- --ignored
```

Important tests cover:

- production parameter validation and the `2^-132` gate
- Circle FFT domain and interpolation checks
- ECDSA circuit tamper rejection
- fixed and hidden claim binding
- MAC mismatch rejection
- mandatory revocation digest and signature binding

## File map

| Path | Purpose |
|---|---|
| `src/circuit.rs` | Layered circuit and quadratic gates |
| `src/sumcheck.rs` | GKR reduction |
| `src/circle_fft.rs` | Circle domains and FFT encoding |
| `src/ligero.rs` | Commitment, masks, proximity, and claim batches |
| `src/merkle.rs` | Column Merkle tree |
| `src/ecdsa.rs` | ECDSA circuits, projections, bundles, and verification |
| `src/mac.rs` | `GF(2^128)` arithmetic and tags |
| `crates/eu-id-prover/src/mdoc_mac.rs` | Outer M31 MAC components |
