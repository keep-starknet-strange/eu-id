# P-256 ECDSA Verification AIR: Full Fake-GLV Spec (v8)

## Scope

This document specifies the AIR for verifying one P-256 ECDSA signature using Garaga-style fake-GLV certificates, implemented as a single dynamic EcdsaVm component with static lookup tables.

The AIR proves:

```text
s * u1 = z_red mod n
s * u2 = r     mod n
H1 = [u1]G    (fake-GLV certificate)
H2 = [u2]Pub  (fake-GLV certificate)
R = H1 + H2
R != O
x(R) mod n = r
```

For nonzero scalars, each certificate uses the fake-GLV argument:

```text
s1 + S * s2_signed = 0 mod n
[s1]P + [s2_abs]H_signed = O
0 < s1 < 2^128
0 < s2_abs < 2^128
```

This implies `H = [S]P` because P-256 has prime order and cofactor 1.

If `S = 0`, the certificate takes a zero-scalar branch enforcing `H = O`.

## Rejected Alternatives

| Alternative | Reason rejected |
|---|---|
| Two independent deterministic scalar multiplications `[u1]G` and `[u2]Q` | Wastes two full 256-bit chains. Garaga's fake-GLV certificate verifies each scalar multiplication with much smaller signed components. |
| Width-5 Shamir/Horner chain for `[u1]G + [u2]Q` | Good deterministic fallback, but still performs 260 doublings and 104 mixed-add slots. Garaga's hinted scalar-mul verification is the better primary design. |
| Witness `R` and prove `[s]R = [z]G + [r]Q` | Removes three scalar-field multiplications but adds a third scalar/base to the group equation. The group work dominates, so this is worse. |
| Generic `q * p + r` reduction for every base-field multiplication | Base-field multiplications dominate EC arithmetic. P-256 has a Solinas modulus, so generic quotient multiplication is avoidable. |
| Full combined table `[d1]G + [d2]Q` for every window | With `w = 5`, this is `2^10 = 1024` variable table entries per public key. Worse than fake-GLV certificate verification for single signatures. |
| Poseidon-based signature scheme | Must use real P-256 ECDSA; no hash-based alternatives. |

## Constants

```text
p  = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
n  = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
a  = -3 mod p
b  = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
Gx = 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
Gy = 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5
M31_MOD = 2^31 - 1
```

Representation:

```text
LIMB_BITS = 13
N_LIMBS   = 20
value     = sum limb[i] * 2^(13*i) for i in 0..19
```

All untrusted limbs are range-checked via `Range13`. Products of two 13-bit values sum at most 20 terms: `20 * (2^13 - 1)^2 < 2^31`, fitting M31.

Key inequality: `p < 2n`, so `x(R) mod n` requires at most one subtraction of `n`.

## Public Inputs

Required tuple:

```text
(sig_id, z, r, s, pub_x, pub_y)
```

Optional extension with recovery id:

```text
(sig_id, z, r, s, pub_x, pub_y, recovery_id)
```

Bound through `PublicEcdsaInstance` relation:

```text
PublicData yields:    -1 * PublicEcdsaInstance(sig_id, ...)        in initial_logup_sum  (provider: negative)
EcdsaVm uses:        +sig_active * PublicEcdsaInstance(sig_id, ...) in the PUBLIC_BIND row  (consumer: positive)
```

`sig_id` is schedule-determined and preprocessed. Public inputs are an ordered
batch, not an unordered multiset. Including `sig_id` permits two signatures in
the same batch to have identical `(z, r, s, pub_x, pub_y[, v])` values without
colliding in the public-input relation, while still preventing a row for one
signature from consuming another signature's public tuple.

Use distinct relation tags for the base and recovery variants to prevent collisions.

If `recovery_id` is bound, it represents the full two-bit value:

```text
recovery_id = odd_y + 2 * x_ge_n
```

This differs from Garaga's parity-style check `is_even(R.y) != v` which uses a single bit. If interoperating with Garaga callers, support two distinct modes:

```text
GaragaParityV:    v = odd_y                    (1-bit parity, Garaga-compatible)
FullRecoveryId:   recovery_id = odd_y + 2*x_ge_n  (2-bit, full recovery)
```

Use separate public relation tags for each mode.

## Top-Level Statement

For each enabled signature, the AIR enforces:

1. Public binding via `PublicEcdsaInstance`.

2. Digest is 256 bits (semantics: `z` is the message digest hash output, typically SHA-256(message), interpreted as a big-endian unsigned integer):

```text
z_limb[19] < 2^9                         (via Range9 lookup)
```

3. Digest reduction:

```text
z - z_red - z_ge_n * n = 0               (integer equation with carries)
z_ge_n in {0, 1}
0 <= z_red < n                           (canonical, via borrow witness)
```

4. Signature ranges:

```text
1 <= r < n
1 <= s < n
```

Enforced by: `r - 1` and `s - 1` are valid non-negative limb decompositions (range-checked), plus `r < n` and `s < n` via borrow witnesses.

5. Public key validity:

```text
pub_x < p                                (canonical, via borrow witness)
pub_y < p                                (canonical, via borrow witness)
pub_y^2 = pub_x^3 - 3*pub_x + b mod p
Pub.inf = 0
```

6. Scalar setup (no `s_inv`):

```text
s * u1 = z_red mod n
s * u2 = r     mod n
```

Since `1 <= s < n` and `n` is prime, `s` is invertible, so these uniquely determine `u1, u2`.

7. Fake-GLV certificates:

```text
FakeGlvCert(cert=0, P=G,   S=u1, H=H1)
FakeGlvCert(cert=1, P=Pub, S=u2, H=H2)
```

8. Final EC addition and comparison:

```text
R = H1 + H2
R != O
x(R) - r - x_ge_n * n = 0
x_ge_n in {0, 1}
```

## Architecture: Single EcdsaVm Component

All dynamic rows live in one physical stwo component. Static lookup tables are separate components.

Rationale: proof size scales with total committed columns across all physical components. Merging all dynamic rows into one component minimizes committed columns by reusing limb slots across row types.

### Physical components

```text
EcdsaVm             dynamic, all signature logic
Range13              preprocessed values, witness multiplicity column, 2^13 rows
Range9               preprocessed values, witness multiplicity column, 2^9 rows
Range11               preprocessed values, witness multiplicity column, 2^11 rows (top limb of 128-bit values)
Range7              preprocessed values, witness multiplicity column, 2^7 = 128 rows (use_count bounds, valid 0..127)
Selector4x4          preprocessed values, witness multiplicity column, 16 rows
Selector16Decode     preprocessed values, witness multiplicity column, 16 rows
FinalSelector        preprocessed values, witness multiplicity column, 4 rows
SignedCarryRange     preprocessed values, witness multiplicity column, sized per carry bound
```

For all static lookup tables: the table values (range entries, selector tuples) are preprocessed and circuit-fixed. The multiplicity columns are witness data computed by the trace generator from the actual number of uses per entry. This is standard stwo static-lookup practice.

Booleans use polynomial constraints `b*(1-b)=0`, not a lookup table.

### Row type selectors

Row types are identified by preprocessed one-hot selector columns, not a dynamic `row_type` field. Since the row schedule is fixed for a given signature count, these selectors are circuit-determined:

```text
is_public_bind(row)
is_scalar_setup(row)
is_fake_glv_scalar(row)
is_selector_recon(row)
is_cert_bind(row)
is_on_curve(row)
is_state_load(row)
is_ec_double(row)
is_ec_add(row)
is_msb_select(row)
is_affine_export(row)
is_lsb_select(row)
is_final_check(row)
```

Making row-type selectors preprocessed saves one dynamic column and prevents malicious row-type switching. Branch choices like `scalar_is_zero` remain witness booleans.

Row types:

```text
PUBLIC_BIND
SCALAR_SETUP
FAKE_GLV_SCALAR
SELECTOR_RECON
CERT_BIND
ON_CURVE
STATE_LOAD
EC_DOUBLE
EC_ADD
MSB_SELECT
AFFINE_EXPORT
LSB_SELECT
FINAL_CHECK
```

Constraints are gated by their preprocessed row-type selector. Shared column slots are reused across types.

## Shared Row Schema

```text
enabler                           1 col
sig_active                        1 col   (materialized: = enabler)
cert_active                       1 col   (materialized: = enabler * scalar_is_nonzero)
cert_zero_active                  1 col   (materialized: = enabler * scalar_is_zero)

state point (homogeneous projective, NO inf flag):
  X[20], Y[20], Z[20]            60 cols

operand point (affine + inf):
  Ux[20], Uy[20], Uinf           41 cols

bigint slots:
  A[20], B[20], C[20]            60 cols

quotient / correction:
  Q[10..21]                       10-21 cols

flags and selectors:
  selector flags, sign bits,
  boolean witnesses, is_lsb_00,
  lsb00_active                     ~22 cols

carries:
  carry[20..40]                   20-40 cols
```

Row-type selectors (`is_public_bind`, `is_ec_double`, etc.) are preprocessed (not in the dynamic column count).

Schedule-determined identifiers (`sig_id`, `cert_id`, `step_id`) are preprocessed columns, not dynamic witnesses. Since the row schedule is fixed for a given signature count, these values are circuit-determined and making them preprocessed prevents a prover from relabeling rows in the PreparedPoint relation.

### Active gate definitions

The branch flags are certificate-wide values sourced from that certificate's
`CERT_BIND` row. Every row belonging to the certificate must copy
`scalar_is_zero` and `scalar_is_nonzero` from the schedule-fixed `CERT_BIND`
row via fixed-schedule offset constraints before using them in gate equations,
LogUp numerators, disabled-row constraints, or EC transition gates. This copy
is mandatory: branch flags are not independent row-local witnesses.

The branch flags must depend on `enabler` on every certificate row:

```text
scalar_is_zero + scalar_is_nonzero = enabler
scalar_is_zero * (scalar_is_zero - 1) = 0
scalar_is_nonzero * (scalar_is_nonzero - 1) = 0
```

Three materialized gate columns:

```text
sig_active = enabler
    Used for: PUBLIC_BIND, SCALAR_SETUP, FINAL_CHECK, ON_CURVE(Pub),
    and any row active regardless of which certificate's zero/nonzero branch.

cert_active = enabler * scalar_is_nonzero
    Used for: fake-GLV prep/chain/LSB rows, ON_CURVE(H), AFFINE_EXPORT,
    PreparedPoint emissions/consumptions, Selector4x4/Selector16Decode/FinalSelector
    lookups, nonzero-branch Range13 uses, EC formula gates, previous-row
    transition gates. This replaces the previous `row_active`.

cert_zero_active = enabler * scalar_is_zero
    Used for: zero-branch constraints (S limbs = 0, H = O).
```

Each gate is a materialized witness column constrained by its defining equation. Do not use inline products in LogUp numerators or high-degree gates. Use the gate columns linearly everywhere.

Certificate-wide branch binding:

```text
For each row in certificate (sig_id, cert_id):
    scalar_is_zero(row)    = scalar_is_zero(CERT_BIND(sig_id, cert_id))
    scalar_is_nonzero(row) = scalar_is_nonzero(CERT_BIND(sig_id, cert_id))
```

The implementation may enforce this with fixed-schedule offset masks because
the row schedule and the `CERT_BIND` row for each certificate are circuit-fixed.
Do not replace this with unconstrained witness reuse. Without this binding, a
malicious prover could make `CERT_BIND` take one branch while disabling the
fake-GLV prep/chain/final-cert rows with different branch flags.

This keeps numerator degree at 1, which is critical for LogUp batching: stwo's `finalize_logup_in_pairs` doubles the number of fractions per interaction column, but the batched degree grows with numerator degree. Keeping numerators linear ensures paired degree stays at 2, well under D <= 4.

Estimated peak width: ~350-500 M31 dynamic columns depending on the widest row type, plus interaction columns.

### Coordinate model

Internal EC state uses **homogeneous projective coordinates** (RCB model):

```text
Curve equation: Y^2 Z = X^3 - 3 X Z^2 + b Z^3
Affine recovery: x = X/Z, y = Y/Z
```

This is NOT Jacobian. Jacobian uses `x = X/Z^2, y = Y/Z^3`. All affine export, final check, and projective-affine equivalence formulas must use the homogeneous model. This aligns with RCB Algorithms 4/5/6 which are stated in homogeneous projective coordinates.

Internal projective state has **no `inf` flag**. The point at infinity is represented as:

```text
O_proj = (0, 1, 0)
```

which satisfies the homogeneous curve equation: `1^2 * 0 = 0^3 - 3*0*0^2 + b*0^3 = 0`. Finite points have `Z != 0`.

**Forbidden representation**: `(0, 0, 0)` is NOT a valid projective point. In projective space, `(0:0:0)` does not represent any point. The RCB paper explicitly notes that the point at infinity maps to `(0:0:0)` in certain formula outputs and marks it as not belonging to the target projective space. Any EC formula output or intermediate state must satisfy the projective invariant `(X, Y, Z) != (0, 0, 0)`.

Valid projective points:

```text
Finite:    Z != 0               (affine point (X/Z, Y/Z) on curve)
Infinity:  X = 0, Z = 0, Y != 0 (canonical: (0, 1, 0))
Forbidden: X = 0, Y = 0, Z = 0  (not a projective point)
```

### Canonical point representations

Affine points (operands, PreparedPoint bus entries, exported points) carry an `inf` flag:

```text
if inf = 0:
    x < p      (canonical, via borrow witness)
    y < p      (canonical, via borrow witness)
if inf = 1:
    x = 0
    y = 0
```

Projective internal state has no `inf` flag:

```text
Finite point:   Z != 0
Infinity:       X = 0, Z = 0, Y != 0  (canonical load: (0, 1, 0))
```

The distinction: affine `inf` flags exist only at boundaries (STATE_LOAD from affine, AFFINE_EXPORT, PreparedPoint bus, operand slots). Internal EC chain state is pure homogeneous projective — no per-row `inf` tracking.

### Projective infinity detection

Without `state.inf`, infinity detection happens only at boundary rows:

```text
1. STATE_LOAD: converts affine (x, y, inf) to projective, setting
   (0, 1, 0) for infinity, (x, y, 1) for finite (see STATE_LOAD).
2. EC_DOUBLE (RCB Algorithm 6) and EC_ADD (RCB Algorithm 5):
   the RCB complete formulas never produce (0, 0, 0). For P+(-P),
   Algorithm 4/5 produces a valid projective infinity with Z_out = 0,
   Y_out != 0. For DOUBLE(O), Algorithm 6 must be verified to produce
   valid projective infinity (not (0,0,0)). No explicit inf check
   needed mid-chain — the formulas maintain the projective invariant.
3. AFFINE_EXPORT: witnesses state_is_inf boolean. If state_is_inf = 1,
   must prove Z = 0, X = 0, AND Y != 0 (via Y * Y_inv = 1 mod p).
   If state_is_inf = 0, must prove Z != 0 (via Z * Z_inv = 1 mod p).
4. FINAL_CHECK: proves Z_R != 0 via Z_R * Z_R_inv = 1 mod p (R != O).
5. Certificate final equivalence: proves Z_acc != 0 via
   Z_acc * Z_acc_inv = 1 mod p (since R3 is finite, Acc must be finite),
   then cross-multiplication X_acc = x_r3 * Z_acc, Y_acc = y_r3 * Z_acc.
```

This eliminates the per-EC-row `inf_out iff Z_out = 0` consistency problem entirely. The RCB formulas algebraically handle infinity through the projective representation without needing an explicit flag. The `(0,0,0)` prohibition is enforced by: (a) STATE_LOAD never produces it, (b) RCB formulas never produce it for valid projective inputs, (c) boundary checks (AFFINE_EXPORT, cert equivalence, FINAL_CHECK) verify the projective invariant.

## Dataflow Model

With all dynamic rows in one physical component and no high-arity logup relations for EC state points, values must flow between non-adjacent rows through explicit mechanisms. The spec uses a hybrid approach:

**Previous-row constraints (Pattern B)**: For the long EC chain (DOUBLE, DOUBLE, ADD sequences), each row reads `state` from the previous row. This is the primary data-flow mechanism for chain execution. Requires `bit_reverse_coset_to_circle_domain_order` on all cross-row columns. Boundary indicators gate the first row of each segment.

**Fixed-schedule offset constraints**: For short-range connections where the row distance is fixed and known at circuit-compile time (e.g., SCALAR_SETUP row 0 → FAKE_GLV_SCALAR row 0 for `u1`), use offset masks at the known distance. Only practical for small, fixed offsets.

**PreparedPoint copy bus** (counted logup relation): For the prepared table base points computed during table preparation and consumed by the chain. Points enter the bus as affine coordinates after AFFINE_EXPORT. The relation carries:

```text
PreparedPoint(sig_id, cert_id, table_index, x[20], y[20], inf)
```

AFFINE_EXPORT rows yield each base point with dynamic multiplicity equal to its total use count. Chain ADD rows, MSB init, LSB correction, and Table[16] construction consume the selected point with multiplicity +1.

Including `sig_id` prevents cross-signature table reuse bugs when batching multiple signatures.

**What is NOT connected by logup**: Internal polynomial constraints (scalar equations, EC formulas, Solinas reductions, canonical comparisons) are enforced row-locally. The chain's previous-row state transitions are polynomial constraints, not logup.

### Specific dataflow paths

All dataflow mechanisms are frozen; no implementation-choice alternatives remain.

```text
PUBLIC_BIND.z/r/s/pub  -> SCALAR_SETUP rows             (fixed-schedule offset)
PUBLIC_BIND.pub_x/y    -> cert 1 prep first STATE_LOAD   (fixed-schedule offset; loads Pub
                                                          as the initial projective state for
                                                          the [2]Pub/[3]Pub computation; cert 0
                                                          uses preprocessed G constants instead)
SCALAR_SETUP.u1/u2     -> FAKE_GLV_SCALAR rows           (fixed-schedule offset)
SCALAR_SETUP.u1/u2     -> CERT_BIND branch constraints   (fixed-schedule offset)
CERT_BIND branch flags -> every row in that certificate  (fixed-schedule offset)
CERT_BIND.H_x/H_y      -> FAKE_GLV_SCALAR.R_x/R_y         (fixed-schedule offset + sign-
                                                          conditional negation by s2_sign_bit;
                                                          see "R = H_signed materialization")
FAKE_GLV_SCALAR.s1/s2  -> SELECTOR_RECON rows            (fixed-schedule offset)
FAKE_GLV_SCALAR.R      -> prep STATE_LOADs for [2]R/[3]R  (fixed-schedule offsets; R is the
                          and Base[i] EC_ADD operand slots second operand for all 9 prep ADDs
                          that combine P-factors with R)   plus the 1-2 prep doublings)
H1/H2 coordinates      -> final H1+H2 add                (STATE_LOAD + previous-row)
Prep EC outputs        -> AFFINE_EXPORT -> PreparedPoint bus (affine, copy bus)
PreparedPoint bus      -> chain operands                  (copy bus consumption)
R3 affine              -> Table[16] ADD operand            (fixed-schedule offset from R3's AFFINE_EXPORT row)
R3 affine              -> cert final projective eq check   (fixed-schedule offset from R3's AFFINE_EXPORT row)
H1/H2 affine witness   -> final H1+H2 addition            (fixed-schedule offset from H1/H2's CERT_BIND rows)
H1/H2 CERT_BIND coords -> ON_CURVE check                  (fixed-schedule offset, nonzero branch only)
selector chunks        -> chain ADD row selection          (fixed-schedule offset)
selector_0             -> Table[16] construction           (fixed-schedule offset)
```

### R = H_signed materialization

R is the sign-adjusted base point used by every prep EC operation that combines
a P-factor with an R-factor. It is a derived witness, not a hint:

```text
R_x = H_x                                             (always)
R_y = (1 - s2_sign_bit) * H_y + s2_sign_bit * (p - H_y)
R_inf = H_inf                                         (negation of O is O)
```

The witness columns `R_x[20], R_y[20], R_inf` live in the FAKE_GLV_SCALAR row
(co-located with `s2_sign_bit`). H limbs are copied in from that certificate's
CERT_BIND row by fixed-schedule offset. The conditional negation is enforced
per-limb against a witnessed `H_y_neg[20]` that satisfies `H_y + H_y_neg = p`
(carry-checked, with `H_y_neg` zero when `H_inf = 1` to preserve canonical
infinity). On the zero branch (`scalar_is_zero = 1`), all R limbs are forced
to zero and `R_inf = 1`, gated by `cert_zero_active`.

Every downstream prep STATE_LOAD or EC_ADD operand slot that needs R reads its
limbs by fixed-schedule offset from this row. R does NOT enter the PreparedPoint
bus.

R3 dataflow: R3 is used in exactly two places per certificate: (1) as the EC_ADD operand during Table[16] construction, and (2) as the reference for the certificate final projective-affine equivalence check. Both access R3 via fixed-schedule offsets from the R3 AFFINE_EXPORT row. R3 does NOT enter the PreparedPoint bus.

H1/H2 dataflow: H1 and H2 are **hinted affine witness points**, not outputs of EC operations. Each certificate proves `H = [S]P` by verifying `[s1]P + [s2_abs]H_signed = O` — the certificate does not compute H, it verifies it. The same affine H coordinates are used in three places per certificate:

```text
1. H_signed construction (conditional negation based on s2_sign_bit)
2. ON_CURVE check (H_y^2 = H_x^3 + a*H_x + b mod p)
3. Final H1+H2 addition (loaded via STATE_LOAD)
```

After both certificates complete, H1 and H2 are loaded via STATE_LOAD from their respective CERT_BIND rows (fixed-schedule offsets) for the final `R = H1 + H2` addition. H1/H2 do NOT have AFFINE_EXPORT rows — they are already affine witness inputs. Loading from CERT_BIND (not ON_CURVE) is necessary because the zero branch has no active ON_CURVE row for H, but CERT_BIND always binds the point including the `inf` flag.

## Row Types

### PUBLIC_BIND

Binds public inputs to the proof and validates all input ranges. Conceptually one unit per signature; may physically span 2-4 rows if the arithmetic (carry chains, borrow witnesses) does not fit in a single row.

Columns used: `A = z[20], B = r[20], C = s[20]`, operand slots for `pub_x[20], pub_y[20]`, bigint slots for witnesses, carries.

Constraints:

```text
enabler * (enabler - 1) = 0

z_limb[19] < 2^9                                    (Range9 lookup)

z - z_red - z_ge_n * n = 0                          (integer equation with carries)
z_ge_n in {0, 1}
0 <= z_red < n                                      (borrow witness)

r - 1 = r_minus_one                                 (range-checked limbs)
r < n                                               (borrow witness)
s - 1 = s_minus_one                                 (range-checked limbs)
s < n                                               (borrow witness)

pub_x < p                                           (borrow witness)
pub_y < p                                           (borrow witness)
Pub.inf = 0                                         (direct constraint)
```

Relation consumption (consumer: positive sign):

```text
+sig_active * PublicEcdsaInstance(sig_id, z, r, s, pub_x, pub_y[, v])
```

If the arithmetic exceeds a single row's width, split into PUBLIC_BIND (relation emission + top-limb check) and INPUT_VALIDATE (reduction + range checks). The exact split is an implementation decision; the constraints above must all be enforced.

### SCALAR_SETUP

Two rows per signature: `s*u1 = z_red mod n` and `s*u2 = r mod n`.

Columns used: `A = first_operand[20], B = second_operand[20], C = result[20], Q = quotient[20/21]`, carries.

Constraint (full 256x256 FnMul):

```text
A * B - Q * n - C = 0          (limb-by-limb with carry propagation)
0 <= A, B, C < n               (borrow witnesses)
0 <= Q < n                     (borrow witness)
```

Bounding `Q < n` is not strictly necessary if the integer equality and carry bounds are exact, but it reduces carry/headroom risk and simplifies the M31 headroom audit. Since `0 <= A, B < n`, the true quotient satisfies `0 <= Q < n`; constraining it makes the AIR match this bound.

### FAKE_GLV_SCALAR

One row per certificate (2 per signature). Proves the scalar equation using a signed 256-by-128 small multiplication.

For `s2_sign_bit = 0`:

```text
S * s2_abs + s1 - q * n = 0
```

For `s2_sign_bit = 1`:

```text
S * s2_abs - s1 - q * n = 0
```

Combined:

```text
S * s2_abs + (1 - 2*s2_sign_bit) * s1 - q * n = 0
```

Key bounds:

```text
0 < s1 < 2^128       (10 limbs: 9 full + top < 2^11)
0 < s2_abs < 2^128   (same)
0 <= q < 2^128        (non-negative, top limb bounded)
s2_sign_bit in {0, 1}
```

The `q >= 0` and `q < 2^128` bounds require careful top-limb treatment. Ten 13-bit limbs allow values up to `2^130 - 1`, not `2^128 - 1`. Enforce:

```text
q[0..8]   < 2^13     (Range13 lookup, 9 limbs)
q[9]      < 2^11     (Range11 lookup — top limb)
q[10..19] = 0        (direct zero constraints)
```

This gives `q < 2^(9*13 + 11) = 2^128`. Without the top-limb bound, the scalar equation could be satisfied with `q` values up to `2^130`, breaking the integer-level soundness argument.

The `q >= 0` bound follows from all limbs being non-negative (range-checked). This is important for the `s2_abs != 0` and `S != 0` soundness argument: the scalar equation is an integer equation, so `q` must be non-negative for the implication to hold.

The `s1 > 0` enforcement: witness `s1_minus_one = s1 - 1`, range-check all its limbs. This proves `s1 >= 1`. Combined with the scalar equation and `n` prime, this implies `S != 0` and `s2_abs != 0`, making separate inverse checks unnecessary.

Upper limbs of `s1`, `s2_abs`, `q` (positions 10..19) must be constrained to zero.

Since `s1` and `s2_abs` are reconstructed from selector bits (see Selector Decomposition), the `< 2^128` range is already proven by the reconstruction. The `> 0` check via `s1_minus_one` is still needed.

### SELECTOR_RECON

Eight rows per certificate (16 per signature). Each row packs multiple 2-bit selector chunks.

See the Selector Decomposition section for the full reconstruction constraints.

### CERT_BIND

One row per certificate (2 per signature). Binds the hinted point `H` and witnesses the zero/nonzero branch:

```text
H_x[20], H_y[20], H_inf, scalar_is_zero, scalar_is_nonzero
```

Constraints:

```text
scalar_is_zero and scalar_is_nonzero are copied from this row to every
row in the certificate via fixed-schedule offset constraints.

Nonzero branch (scalar_is_nonzero = 1):
    H_inf = 0                                (H is finite)
    H_x < p, H_y < p                        (canonical)

Zero branch (scalar_is_zero = 1):
    S_limb[i] = 0 for all i                  (S loaded by fixed-schedule offset)
    H_inf = 1
    H_x[i] = 0   for all i
    H_y[i] = 0   for all i
```

`CERT_BIND` must receive the certificate scalar `S` (`u1` for cert 0, `u2` for
cert 1) from `SCALAR_SETUP` via fixed-schedule offset. The zero branch is valid
only when that scalar is exactly zero. The nonzero branch does not need a
separate `S != 0` inverse: with branch binding, the fake-GLV scalar equation and
`s1 > 0` make `S = 0` unsatisfiable.

The final `H1 + H2` addition loads H1 and H2 from their CERT_BIND rows via fixed-schedule offset (not from ON_CURVE rows). This is necessary because the zero branch (e.g., `u1 = 0`, `H1 = O`) has no active ON_CURVE row for H, but the `H1 + H2` addition still needs to know whether H is infinity. CERT_BIND is always present and always binds H, regardless of branch.

### ON_CURVE

Proves a point lies on the P-256 curve. Used for:

```text
Pub:  pub_y^2 = pub_x^3 + a*pub_x + b mod p   (always, gated by sig_active)
H1:   H1_y^2 = H1_x^3 + a*H1_x + b mod p     (nonzero branch only, gated by cert_active)
H2:   H2_y^2 = H2_x^3 + a*H2_x + b mod p     (nonzero branch only, gated by cert_active)
```

H1/H2 on-curve checks are gated by `cert_active` because in the zero branch, H = O and affine infinity is not an on-curve point. The H coordinates checked here must match those in the corresponding CERT_BIND row (enforced by fixed-schedule offset).

Each ON_CURVE check uses Fp arithmetic (Solinas reduction) to verify the curve equation. This requires ~3 Fp multiplications (x^2, x^3, y^2) plus linear combinations. If these do not fit in a single row, split across 2-3 rows.

### STATE_LOAD

Writes a point into the `state` slot without performing an EC operation. Used when the next EC row needs a left input that is not the previous row's output.

```text
state.X = source.X
state.Y = source.Y
state.Z = source.Z
```

The source may come from:

- A fixed-schedule offset (e.g., loading P3 before a table-preparation ADD)
- The PreparedPoint copy bus (loading an affine base point as projective with Z=1)
- A constant (preprocessed G, [2]G, [3]G)

When loading an affine point from the PreparedPoint bus as projective state:

```text
if aff.inf = 0:
    state = (aff.x, aff.y, 1)         (finite: lift to projective with Z = 1)
if aff.inf = 1:
    state = (0, 1, 0)                  (infinity: canonical O_proj)
```

The conversion is constrained per-limb:

```text
state.X[i] = (1 - aff.inf) * aff.x[i]             for all i
state.Y[i] = (1 - aff.inf) * aff.y[i] + aff.inf * delta(i, 0)    for all i
state.Z[i] = (1 - aff.inf) * delta(i, 0)           for all i
```

where `delta(i, 0)` is 1 when `i = 0` and 0 otherwise (placing the value `1` in the lowest limb). The `aff.inf` flag is boolean-constrained.

STATE_LOAD is required for table preparation, where the left input jumps between P, P3, R, R3, and table entries. STATE_LOAD rows also serve as segment boundaries: the next EC_DOUBLE or EC_ADD row reads from this row via previous-row transition, starting a new chain segment.

### EC_DOUBLE

Computes `state_next = [2]state` using the RCB exception-free doubling formula for short Weierstrass `a = -3` (Renes-Costello-Batina **Algorithm 6**).

Algorithm 6 is the dedicated doubling formula. Algorithm 4 is the complete *addition* formula; using Algorithm 4 with both inputs equal also works but is less efficient than Algorithm 6.

Uses previous-row transition: row `i` reads `state` from row `i-1` and writes the doubled result to its own `state`.

The first row of a segment must be gated by a boundary indicator to prevent reading the previous segment's last row. In practice, STATE_LOAD rows serve as these boundaries.

**Algorithm 6 (dbl-2015-rcb-3) explicit steps.** Renes-Costello-Batina exception-free doubling, specialized for `a = -3`. Cost: 8M + 3S + 2 multiplications-by-`b` + 21 additions. Each line is a Fp operation (mul, add, sub, or subtract a constant); each is enforced by a Solinas reduction equation per the M31 headroom audit, with degree-2 intermediates if a single line exceeds the centered M31 limit.

```text
Input:  (X1, Y1, Z1)
Output: (X3, Y3, Z3) = [2](X1, Y1, Z1)

t0 = X1 * X1
t1 = Y1 * Y1
t2 = Z1 * Z1
t3 = X1 * Y1
t3 = t3 + t3
Z3 = X1 * Z1
Z3 = Z3 + Z3
Y3 = b  * t2
Y3 = Y3 - Z3
X3 = Y3 + Y3
Y3 = X3 + Y3
X3 = t1 - Y3
Y3 = t1 + Y3
Y3 = X3 * Y3
X3 = X3 * t3
t3 = t2 + t2
t2 = t2 + t3
Z3 = b  * Z3
Z3 = Z3 - t2
Z3 = Z3 - t0
t3 = Z3 + Z3
Z3 = Z3 + t3
t3 = t0 + t0
t0 = t3 + t0
t0 = t0 - t2
t0 = t0 * Z3
Y3 = Y3 + t0
t0 = Y1 * Z1
t0 = t0 + t0
Z3 = t0 * Z3
X3 = X3 - Z3
Z3 = t0 * t1
Z3 = Z3 + Z3
Z3 = Z3 + Z3
```

**DOUBLE(O) is sound.** Substituting `(X1, Y1, Z1) = (0, 1, 0)` and tracing the schedule symbolically: `t0 = t2 = t3 = Z3 = 0`, `t1 = 1`, so `Y3 = 1 - 0 = 1` after the early `X3, Y3 ← (t1 − ..., t1 + ...)` lines and remains `1` after all later additions of `0 · _` terms; `X3` and `Z3` stay `0` throughout (every multiplicative term has a 0 factor). Output `(0, 1, 0)` — the canonical projective infinity, never the forbidden `(0, 0, 0)`. **No explicit conditional needed** for DOUBLE(O).

Columns: state point (X, Y, Z) + formula intermediates in bigint/carry slots.

### EC_ADD

Computes `state_next = state_prev + operand` using the RCB complete mixed addition formula for short Weierstrass `a = -3` (Renes-Costello-Batina **Algorithm 5**), with explicit operand-infinity conditional.

Algorithm 5 is the complete *mixed* addition formula where the second input has `Z2 = 1`. This is the natural choice because all operands are affine (from the PreparedPoint bus). Algorithm 4 is the general complete addition for two projective inputs; it would also work but costs more multiplications.

EC_ADD must be complete for all input combinations:

```text
O + P       (state_prev is infinity, operand is finite)
P + O       (state_prev is finite, operand is infinity)
P + P       (state_prev equals operand — doubling case)
P + (-P)    (state_prev is negation of operand — result is O)
P + Q       (generic, no special relationship)
```

Algorithm 5 handles cases 1, 3, 4, 5 algebraically: it produces correct projective output including a valid projective infinity (Z_out = 0, Y_out != 0) for P+(-P), correct doubling for P+P, and correct `O + P` when state_prev is a valid projective infinity (Z1 = 0, Y1 != 0). The formula never produces `(0, 0, 0)` for valid projective inputs.

The only case requiring explicit conditional is **P + O** (operand is infinity, `Uinf = 1`), because the operand is affine and lifting O to projective `(0, 1, 0)` with `Z2 = 0` would lose the mixed-add optimization (Algorithm 5 assumes `Z2 = 1`). Handle with conditional assignment:

```text
if Uinf = 1:
    state_next = state_prev                    (adding O is identity)
else:
    state_next = RCB_Algorithm5(state_prev, (Ux, Uy, 1))
```

The conditional assignment is constrained per-limb:

```text
state_next.X[i] = Uinf * state_prev.X[i] + (1 - Uinf) * formula_X[i]
state_next.Y[i] = Uinf * state_prev.Y[i] + (1 - Uinf) * formula_Y[i]
state_next.Z[i] = Uinf * state_prev.Z[i] + (1 - Uinf) * formula_Z[i]
```

There is no `inf_out` flag. The output is pure homogeneous projective `(X, Y, Z)`. If the result is the point at infinity, it has `Z_out = 0` and `Y_out != 0`. This is detected only at boundary rows (AFFINE_EXPORT, FINAL_CHECK), not mid-chain.

**Critical**: The fake-GLV table intentionally has edge cases where `P + R = O` (e.g., S = 1 gives R = -P, so Base[2] = P + (-P) = O), and the chain may encounter accumulator/operand coincidences. Algorithm 5 handles these without branches.

**Algorithm 5 (madd-2015-rcb-3) explicit steps.** Renes-Costello-Batina complete mixed addition with `Z2 = 1`, specialized for `a = -3`. Cost: 11M + 2 multiplications-by-`b` + 23 additions. Inputs: projective `(X1, Y1, Z1)`, affine operand `(X2, Y2)` (with `Z2 = 1` implicit).

```text
Input:  (X1, Y1, Z1), (X2, Y2)         ; Z2 = 1 implicit
Output: (X3, Y3, Z3) = (X1,Y1,Z1) + (X2,Y2,1)

t0 = X1 * X2
t1 = Y1 * Y2
t3 = X2 + Y2
t4 = X1 + Y1
t3 = t3 * t4
t4 = t0 + t1
t3 = t3 - t4
t4 = Y2 * Z1
t4 = t4 + Y1
Y3 = X2 * Z1
Y3 = Y3 + X1
Z3 = b  * Z1
X3 = Y3 - Z3
Z3 = X3 + X3
X3 = X3 + Z3
Z3 = t1 - X3
X3 = t1 + X3
Y3 = b  * Y3
t1 = Z1 + Z1
t2 = t1 + Z1
Y3 = Y3 - t2
Y3 = Y3 - t0
t1 = Y3 + Y3
Y3 = t1 + Y3
t1 = t0 + t0
t0 = t1 + t0
t0 = t0 - t2
t1 = t4 * Y3
t2 = t0 * Y3
Y3 = X3 * Z3
Y3 = Y3 + t2
X3 = t3 * X3
X3 = X3 - t1
Z3 = t4 * Z3
t1 = t3 * t0
Z3 = Z3 + t1
```

**Completeness verification per case** (RCB Theorem 4):

```text
Case        State_prev (proj)    Operand (affine)   Algorithm 5 output         OK
----------------------------------------------------------------------------
O + P       (0, 1, 0)            (X2, Y2)           (X2*Y2, Y2^2, Y2)         yes (= P projectively)
P + P       (X, Y, Z)            (X/Z, Y/Z)         doubled point             yes (matches Alg 6)
P + (-P)    (X, Y, Z)            (X/Z, -Y/Z)        (0, c, 0) with c != 0      yes (canonical proj O)
P + Q       generic              generic            (X1+Q via formula)         yes
P + O       handled by conditional below                                       — (Alg 5 skipped)
```

`O + P` works because `Z1 = 0` collapses all `*Z1` terms; the surviving products evaluate to a projective representative of `(X2, Y2)`. `P + (-P)` produces `Z3 = 0` with `Y3 != 0` (RCB paper Theorem 4); the AIR rejects the forbidden `(0, 0, 0)` only at boundary rows via the existing inverse checks.

Do NOT fall back to an incomplete formula without explicit sign-off and negative tests for P+P and P+(-P).

Columns: state point + operand point + formula intermediates.

### MSB_SELECT

Selects the initial accumulator point for MSB initialization. This is the only use of this row type; chain operand selection is performed inline within chain EC_ADD rows (see Chain Execution).

The 4-way selection uses the FinalSelector lookup to bind `(msb1, msb2)` to both `selector_final` and `init_base_index`. The selected point is loaded from the PreparedPoint bus.

See MSB initialization (Chain Execution section) for full details.

### Chain operand selection (inline in EC_ADD)

Chain ADD rows perform operand selection inline: each ADD row decodes its selector value, fetches the corresponding base point from the PreparedPoint bus, and applies canonical conditional negation. This avoids a separate row type for chain selection.

The selector value from SELECTOR_RECON determines `(base_index, neg_bit)` via the Selector16Decode lookup:

```text
+cert_active * Selector16Decode(selector, base_index, neg_bit)
```

The selected point uses canonical conditional negation:

```text
if inf = 1:
    B = (0, 0, 1)
elif neg_bit = 0:
    B = (Base[base_index].x, Base[base_index].y, 0)
elif neg_bit = 1:
    B = (Base[base_index].x, p - Base[base_index].y, 0)
```

The negated y-coordinate `p - y` is witnessed and verified by a Solinas/Fp equation: `y + y_neg - p = 0` (or equivalently, `y_neg = p - y` via carry-checked subtraction). Do not use `(1 - 2*neg_bit) * y` as that is a field-level expression, not a canonical limb-level Fp value.

Without the Selector16Decode lookup, the prover could reconstruct the scalar correctly but feed the wrong table point into the chain.

### AFFINE_EXPORT

Converts a homogeneous projective EC output to a canonical affine point. Used after every table-preparation EC operation that produces a point entering the PreparedPoint copy bus.

The exporter witnesses a boolean `state_is_inf` to branch between finite and infinite cases:

```text
state_is_inf * (state_is_inf - 1) = 0          (boolean)
```

**Finite case** (`state_is_inf = 0`):

```text
Z_inv exists (witnessed)
Z * Z_inv = 1 mod p              (Fp equation with carries, proves Z != 0)
x_aff = X * Z_inv mod p          (Fp equation with carries)
y_aff = Y * Z_inv mod p          (Fp equation with carries)
x_aff < p                        (canonical, borrow witness)
y_aff < p                        (canonical, borrow witness)
out = (x_aff, y_aff, 0)
```

**Infinite case** (`state_is_inf = 1`):

```text
Z_limb[i] = 0   for all i        (state_is_inf * Z_limb[i] = 0, proves Z = 0)
X_limb[i] = 0   for all i        (state_is_inf * X_limb[i] = 0, proves X = 0)
Y * Y_inv = 1 mod p              (proves Y != 0, preventing (0,0,0))
out = (0, 0, 1)
```

The `state_is_inf` witness is sound because: if `state_is_inf = 0`, the Z inverse proves Z != 0 (finite point). If `state_is_inf = 1`, the Z = 0 and X = 0 constraints plus Y != 0 inverse prove the point is a valid projective infinity (not the forbidden `(0, 0, 0)`). The prover cannot lie in either direction.

Note: this uses **homogeneous** affine recovery `x = X/Z, y = Y/Z`, not Jacobian `x = X/Z^2, y = Y/Z^3`. Finite export still proves three multiplication equations (`Z*Z_inv`, `X*Z_inv`, `Y*Z_inv`), but homogeneous recovery avoids the extra squaring/cubing needed for Jacobian denominators and keeps the equations degree-2.

Relation emission (PreparedPoint provider):

```text
-use_count * PreparedPoint(sig_id, cert_id, table_index, out.x, out.y, out.inf)
```

where `use_count` is the total number of times this point will be consumed by the chain, MSB init, LSB correction, and Table[16] construction (see PreparedPoint Multiplicity Accounting below).

On inactive rows (zero branch), `use_count` must be explicitly constrained to zero:

```text
(1 - cert_active) * use_count = 0
```

For Table[16] specifically:

```text
cert_active * (use_count_16 - 1) = 0     (active => use_count = 1)
(1 - cert_active) * use_count_16 = 0     (inactive => use_count = 0)
```

For Base[i]:

```text
cert_active = 1 => use_count_i in 0..127  (Range7 lookup)
cert_active = 0 => use_count_i = 0        (direct constraint)
```

Do not rely solely on logup imbalance to catch inactive provider emissions; enforce `use_count = 0` explicitly.

AFFINE_EXPORT requires 3 Fp multiplication equations (`Z*Z_inv`, `X*Z_inv`, `Y*Z_inv`) plus canonicalization. If these do not fit in a single row, split across 2 rows. The PreparedPoint emission occurs on the final row of the split.

### LSB_CORRECT (split into LSB_SELECT + EC_ADD)

Two rows per certificate. The LSB correction both selects/negates a correction point and performs an EC addition. For implementation clarity and auditability, this is split into:

```text
Row 1: LSB_SELECT  — 4-way point selection with canonical conditional negation
Row 2: EC_ADD      — Acc = Acc + C (complete addition)
```

**LSB_SELECT** determines the correction point `C`:

```text
(s1_lsb, s2_lsb) = (1,1): C = (0, 0, 1)          [infinity]
(s1_lsb, s2_lsb) = (0,1): C = (P.x, p - P.y, 0)  [-P, non-infinity]
(s1_lsb, s2_lsb) = (1,0): C = (R.x, p - R.y, 0)  [-R, non-infinity]
(s1_lsb, s2_lsb) = (0,0): C = negate(Base[2])      [-(P+R)]
```

For each negated point, witness `y_neg` and verify `y + y_neg = p` (limb-by-limb with carries). If the source point is infinity (`inf = 1`), output `(0, 0, 1)` instead.

Do not emit `p - 0 = p` as a coordinate; that is non-canonical. The infinity flag gates the negation: `inf = 1` forces `x = 0, y = 0`.

For the (0,0) case, Base[2] is consumed from the PreparedPoint bus. The consumption must be conditional on this specific case, not just `cert_active`:

```text
is_lsb_00 - (1 - s1_lsb) * (1 - s2_lsb) = 0       (materialized witness)
lsb00_active - cert_active * is_lsb_00 = 0          (materialized witness)

+lsb00_active * PreparedPoint(sig_id, cert_id, 2, ...)
```

Both `is_lsb_00` and `lsb00_active` are materialized witness columns with their own defining constraints, keeping LogUp numerator degree at 1. Without the conditional, the (0,0) case would always consume Base[2] even when `s1_lsb = 1` or `s2_lsb = 1`, causing a multiplicity imbalance.

**EC_ADD** then computes `Acc = Acc + C` using the complete projective addition (C = O is handled by the EC_ADD completeness cases).

### FINAL_CHECK

One row per signature (may split into 2-4 rows if too wide). Verifies:

```text
Z_R * Z_R_inv = 1 mod p        (proves Z_R != 0, i.e. R != O)
rx = X_R * Z_R_inv mod p       (homogeneous affine x extraction)
rx < p                          (canonical, borrow witness)
rx - r - x_ge_n * n = 0        (limb-by-limb integer equation with carries)
x_ge_n in {0, 1}
```

The Z_R inverse existence proves R is not the point at infinity. No separate `R.inf = 0` flag is needed — with homogeneous projective coordinates and no `inf` flag on internal state, the inverse check is the sole non-infinity proof.

If recovery parity `v` is bound:

```text
ry = Y_R * Z_R_inv mod p       (homogeneous affine y extraction)
ry < p                          (canonical, borrow witness)
```

Exact parity extraction — the LSB of `ry` determines odd/even:

```text
ry_lo = ry_limb[0]                           (13-bit value, range-checked)
ry_lo_half = witness                         (candidate ry_lo / 2)
odd_y = ry_lo - 2 * ry_lo_half              (parity bit)
odd_y * (odd_y - 1) = 0                     (boolean)
ry_lo_half range-checked via Range13         (proves ry_lo_half < 2^13,
                                              hence 2*ry_lo_half <= 2^14 - 2,
                                              which with odd_y in {0,1}
                                              covers ry_lo < 2^14;
                                              but ry_lo < 2^13 from its own
                                              range check, so this is tight)
```

Recovery id assembly:

```text
recovery_id = odd_y + 2 * x_ge_n
recovery_id = v                              (bound via public input)
```

FINAL_CHECK requires 2 Fp multiplication equations without recovery data (`Z_R * Z_R_inv`, `X_R * Z_R_inv`) or 3 with recovery parity (`Y_R * Z_R_inv` as well), plus canonicalization and comparison. If these do not fit in a single row, split across 2-3 rows.

## Fake-GLV Certificate Protocol

### Nonzero branch (`S != 0`)

Given `(P, S, H)` where `H` is the prover's hinted result:

1. Prover supplies `s1, s2_abs, s2_sign_bit` from lattice reduction.

2. Derived values:

```text
s2_signed = s2_abs              if s2_sign_bit = 0
s2_signed = n - s2_abs          if s2_sign_bit = 1

H_signed  = (H_x, H_y)         if s2_sign_bit = 0
H_signed  = (H_x, p - H_y)     if s2_sign_bit = 1
```

Point negation uses canonical `p - y`, not field-level sign flip. If H.inf = 1, H_signed = H (infinity is its own negation with canonical coords (0, 0, 1)).

3. Scalar equation (FAKE_GLV_SCALAR row):

```text
S * s2_abs + (1 - 2*s2_sign_bit) * s1 - q * n = 0
```

4. Nonzero proof: `s1_minus_one >= 0` (range-checked limb decomposition).

5. On-curve checks: `P on curve`, `H on curve`, both non-infinity.

6. Prepared table construction (see below).

7. Chain execution proving `[s1]P + [s2_abs]H_signed = O` (see below).

### Zero branch (`S = 0`)

```text
scalar_is_zero + scalar_is_nonzero = enabler    (see Active gate definitions)
scalar_is_zero * S_limb[i] = 0        for all i
scalar_is_zero * (H_inf - 1) = 0
scalar_is_zero * H_x_limb[i] = 0      for all i
scalar_is_zero * H_y_limb[i] = 0      for all i
```

The nonzero branch constraints are gated by `cert_active` (= `enabler * scalar_is_nonzero`) and do not fire.

### Zero-branch row gating

Because row types are preprocessed and fixed, fake-GLV preparation/chain/LSB rows still exist in the trace even when `S = 0`. The materialized `cert_active` column (see Shared Row Schema / Active gate definitions) gates all nonzero-branch logic:

```text
cert_active - enabler * scalar_is_nonzero = 0    (constraining equation)
```

Use `cert_active` (not `enabler * scalar_is_nonzero` inline) to gate:

- EC formula polynomial constraints on prep/chain rows
- Previous-row transition constraints
- PreparedPoint emissions and consumptions
- Selector4x4, Selector16Decode, FinalSelector lookups on nonzero-branch rows
- Range13 uses for nonzero-only witness columns
- AFFINE_EXPORT gates (including `state_is_inf` branching and use_count)
- Certificate final projective-affine equivalence

**Disabled-row constraints per family**: for disabled rows in the zero branch, each row family must have explicit constraints forcing its witness columns to canonical zero values. This is not just "the prover fills zeros" — without constraints, a malicious prover can write arbitrary values on disabled rows and those values are unconstrained. For each row family:

```text
Row family           Disabled-row constraints
EC_DOUBLE/EC_ADD:    cert_zero_active * state.X[i] = 0, etc. for all witness limbs
AFFINE_EXPORT:       cert_zero_active * use_count = 0 (already above)
                     cert_zero_active * x_aff[i] = 0, cert_zero_active * y_aff[i] = 0
SELECTOR_RECON:      cert_zero_active * a_i = 0, cert_zero_active * b_i = 0
LSB_SELECT/EC_ADD:   cert_zero_active * operand limbs = 0
MSB_SELECT:          cert_zero_active * Acc_init limbs = 0
```

These rows still have their Range13 limb values range-checked (zeros pass trivially) but emit no PreparedPoint or other logup entries because `cert_active = 0`. This prevents half-gated rows with unconstrained values from accidentally entering copy constraints or relation sums.

## Selector Decomposition

Decompose `s1` and `s2_abs` into paired 2-bit chunks:

```text
s1     = s1_lsb + 2 * sum_{i=0}^{62} a_i * 4^i + 2 * 4^63 * s1_msb
s2_abs = s2_lsb + 2 * sum_{i=0}^{62} b_i * 4^i + 2 * 4^63 * s2_msb
```

Where:

```text
s1_lsb, s2_lsb in {0, 1}
s1_msb, s2_msb in {0, 1}
a_i, b_i in {0, 1, 2, 3}        (checked via Selector4x4 lookup)
selector_i = a_i + 4 * b_i
```

This reconstruction proves `s1, s2_abs < 2^128` without a separate range check.

Bit budget: 1 (lsb) + 2*63 (tail) + 1 (msb) = 128 bits per scalar. Matches 10 limbs of 13 bits (130 capacity, top bounded by reconstruction).

Final selector:

```text
selector_final = 5 + s1_msb + 4 * s2_msb
```

Mapping: `(0,0)->5`, `(1,0)->6`, `(0,1)->9`, `(1,1)->10`.

The `selector_final` value is consumed during MSB initialization (not in the chain body). `selector_0` is consumed during Table[16] construction (not in the chain body).

Packed into 8 rows per certificate: 7 rows with 9 chunks each, 1 row with remaining chunks plus lsb/msb data.

## Prepared Table

### Construction

For a nonzero-branch certificate with base point `P` and signed hint `R = H_signed`:

```text
P3 = [3]P               (DOUBLE P -> P2, ADD P2+P -> P3)
R3 = [3]R               (DOUBLE R -> R2_tmp, ADD R2_tmp+R -> R3)
```

For cert 0 (P=G): `[2]G` and `[3]G` are preprocessed constants. Skip 2 EC rows.

Compute 8 base table points (positive versions):

```text
Base[0] = P3 - R        =  3P - R
Base[1] = P  - R        =   P - R
Base[2] = P  + R        =   P + R
Base[3] = P3 + R        =  3P + R
Base[4] = P3 - R3       =  3P - 3R
Base[5] = P  - R3       =   P - 3R
Base[6] = P  + R3       =   P + 3R
Base[7] = P3 + R3       =  3P + 3R
```

All 8 carry an infinity flag: `Base[i] = (x, y, inf)`.

Table preparation requires STATE_LOAD rows to set the left input before each ADD, since the left operand jumps between P, P3, R, R3, and various combinations.

### Affine export of table points

EC operations output projective points. Before entering the PreparedPoint bus, each point must be converted to canonical affine form via AFFINE_EXPORT:

```text
Per certificate (nonzero branch):
  Base[0..7]:  8 AFFINE_EXPORT rows
  R3:          1 AFFINE_EXPORT row
  Table[16]:   1 AFFINE_EXPORT row
  ---
  10 AFFINE_EXPORT rows per cert
```

For 2 certificates: 20 AFFINE_EXPORT rows total.

### The full 16-entry selector-to-point mapping

```text
selector  0 -> (Base[7].x, p - Base[7].y, Base[7].inf)     = -(3P + 3R)
selector  1 -> (Base[6].x, p - Base[6].y, Base[6].inf)     = -(P + 3R)
selector  2 -> (Base[5].x, Base[5].y, Base[5].inf)         =   P - 3R
selector  3 -> (Base[4].x, Base[4].y, Base[4].inf)         =  3P - 3R
selector  4 -> (Base[3].x, p - Base[3].y, Base[3].inf)     = -(3P + R)
selector  5 -> (Base[2].x, p - Base[2].y, Base[2].inf)     = -(P + R)
selector  6 -> (Base[1].x, Base[1].y, Base[1].inf)         =   P - R
selector  7 -> (Base[0].x, Base[0].y, Base[0].inf)         =  3P - R
selector  8 -> (Base[0].x, p - Base[0].y, Base[0].inf)     = -(3P - R)
selector  9 -> (Base[1].x, p - Base[1].y, Base[1].inf)     = -(P - R)
selector 10 -> (Base[2].x, Base[2].y, Base[2].inf)         =   P + R
selector 11 -> (Base[3].x, Base[3].y, Base[3].inf)         =  3P + R
selector 12 -> (Base[4].x, p - Base[4].y, Base[4].inf)     = -(3P - 3R)
selector 13 -> (Base[5].x, p - Base[5].y, Base[5].inf)     = -(P - 3R)
selector 14 -> (Base[6].x, Base[6].y, Base[6].inf)         =   P + 3R
selector 15 -> (Base[7].x, Base[7].y, Base[7].inf)         =  3P + 3R
```

This is encoded in the Selector16Decode preprocessed table which maps each selector value to `(base_index, neg_bit)`. Point negation is `(x, p - y)`, never `(-x, ...)`.

### Table[16] construction dataflow

`Table[16] = Table[selector_0] + R3` is not an ordinary ADD — it requires selection and possible negation:

```text
1. Decode:    selector_0 -> Selector16Decode(selector_0, base_index_0, neg_bit_0)
2. Fetch:     PreparedPoint(sig_id, cert_id, base_index_0, x, y, inf)  [consume]
3. Negate:    apply canonical conditional negation based on neg_bit_0
4. Load:      STATE_LOAD the selected (possibly negated) affine point as projective
5. Add:       EC_ADD with operand = R3 (affine, from R3's AFFINE_EXPORT)
6. Export:    AFFINE_EXPORT the result
7. Publish:   PreparedPoint(sig_id, cert_id, 16, ...) [yield with use_count]
```

R3 enters the ADD as an affine operand (already exported). The result is projective, then affine-exported and published to the PreparedPoint bus as index 16.

Total EC operations for table preparation (EC ops only, excludes STATE_LOAD and AFFINE_EXPORT):

```text
cert 0 (G):   0 DOUBLE (G) + 2 DOUBLE (R) + 9 ADD = 11 EC rows
cert 1 (Pub): 2 DOUBLE (P) + 2 DOUBLE (R) + 9 ADD = 13 EC rows
```

### Infinity in table entries

Valid edge cases produce infinity. When `S = 1`: `H = P`, `R = -P`, so `Base[2] = P + (-P) = O`. When `S = 3` or `S = 3^(-1) mod n`, other entries hit infinity.

All table entries and selected affine points carry `inf` flags. Internal projective accumulators use Z = 0 for infinity (no `inf` flag). Complete projective formulas handle infinity automatically. When affine `inf = 1`: coordinates must be canonical `(0, 0, 1)`, not `(p - 0, ...)`. When projective infinity appears at a boundary load, use canonical `(0, 1, 0)`. EC formula outputs may be any valid homogeneous representative with `X = 0`, `Z = 0`, and `Y != 0`; `(0, 0, 0)` is never valid and must be rejected or avoided by the formula implementation.

Required completeness tests for: `S = 1, n-1, 3, n-3, 3^(-1) mod n, -3^(-1) mod n`.

### Table linking via PreparedPoint copy bus

The prepared table values used by the chain are tied to the AFFINE_EXPORT rows via the `PreparedPoint` counted logup relation.

Each AFFINE_EXPORT row that exports `Base[i]` yields:

```text
-use_count_i * PreparedPoint(sig_id, cert_id, i, x_aff, y_aff, inf)
```

Each chain ADD row that selects `Base[base_index]` consumes:

```text
+cert_active * PreparedPoint(sig_id, cert_id, base_index, Ux, Uy_abs, Uinf)
```

### PreparedPoint multiplicity accounting

The `use_count` for each table index must equal the total number of consumption sites. These include:

```text
For Base[i] (i in 0..7):
  1. MSB initialization (1 use for the selected base point)
  2. Chain body steps 0..61 (variable: each step uses one base point)
  3. Table[16] construction (1 use for the selected base point via selector_0)
  4. LSB correction (0 or 1 use, only Base[2] when (s1_lsb, s2_lsb) = (0,0))

For R3: NOT in the PreparedPoint bus. Accessed via fixed-schedule offset
  from R3's AFFINE_EXPORT row. Used by Table[16] ADD and cert final check.

For Table[16] (index 16):
  1. Fixed final chain step (1 use)
```

The trace generator computes `use_count_i` by scanning the selector stream and counting how many times each `base_index` appears after Selector16Decode mapping, plus MSB, Table[16] construction, and LSB correction uses.

The logup balance ensures every consumed point was actually produced by an AFFINE_EXPORT row with matching coordinates.

### PreparedPoint use_count range constraint

Provider multiplicities must be range-bounded, not arbitrary field values. The maximum per base index is:

```text
62 chain selector uses (steps 0..61, each selects one base_index)
+ 1 MSB init
+ 1 Table[16] construction (selector_0 decodes to one base_index)
+ 1 possible LSB correction (only Base[2])
= 65 maximum
```

Constrain:

```text
0 <= use_count_i <= 127   for Base[i], i in 0..7  (Range7 lookup)
use_count_16 = 1          for Table[16] (exactly one final chain step)
```

The `Range7` lookup table has physical 2^7 = 128 rows (values 0..127). This enforces `use_count < 128`, not `use_count <= 65`. The tighter logical bound 0..65 is guaranteed by logup balance: there are at most 65 consumer sites per base index (62 chain + 1 MSB + 1 Table[16] + 1 LSB), so the total positive multiplicity cannot exceed 65. The provider's negative multiplicity must match exactly for the logup sum to be zero.

Range7's role is to prevent **field-valued multiplicities** (e.g., `use_count = 2^31 - 2` in M31, which could cancel a legitimate provider entry). It does not enforce the exact 65 bound — that comes from the count of consumer sites. If a tighter bound is desired (e.g., for defense in depth), implement a dedicated `UseCountRange(0..65)` table with 2^7 = 128 physical rows (pad 66..127 with zero-multiplicity entries).

Do not carry all 8 base point coordinates through every chain row. That would cost 8 * (20 + 20 + 1) = 328 extra columns per row, blowing the column budget far beyond 500. The copy-bus approach adds only interaction columns (from the logup fractions), keeping original trace columns near ~350-500.

## Chain Execution

### Structure: DOUBLE, DOUBLE, ADD rows

Each chain step computes `Acc_{i+1} = [4]Acc_i + B_i` as three rows:

```text
row 3i+0 (EC_DOUBLE):  state = [2]state_prev
row 3i+1 (EC_DOUBLE):  state = [2]state_prev
row 3i+2 (EC_ADD):     state = state_prev + operand_i
```

Previous-row transitions: each row reads `state` from the row above. This avoids storing both `Acc_in` and `Acc_out`, saving ~61 columns per row.

Requirement: apply `bit_reverse_coset_to_circle_domain_order` to all state columns participating in cross-row masks (Pattern B).

### Segment boundaries

Gate the first row of each segment (cert boundary, prep-to-chain transition) with a boundary indicator so it does not read the previous segment's last row. STATE_LOAD rows serve as natural segment boundaries.

### MSB initialization

The initial accumulator is set by direct selection using `selector_final` and the derived `init_base_index`:

```text
selector_final  = 5 + s1_msb + 4 * s2_msb
init_base_index = 2 + s1_msb + 4 * s2_msb

(s1_msb, s2_msb) = (0,0): selector_final = 5,  init_base_index = 2, Acc_0 = Base[2] = P + R
(s1_msb, s2_msb) = (1,0): selector_final = 6,  init_base_index = 3, Acc_0 = Base[3] = 3P + R
(s1_msb, s2_msb) = (0,1): selector_final = 9,  init_base_index = 6, Acc_0 = Base[6] = P + 3R
(s1_msb, s2_msb) = (1,1): selector_final = 10, init_base_index = 7, Acc_0 = Base[7] = 3P + 3R
```

The FinalSelector lookup is extended to bind both values:

```text
FinalSelector(msb1, msb2, selector_final, init_base_index)
```

with the 4-row preprocessed table:

```text
(0, 0, 5, 2)
(1, 0, 6, 3)
(0, 1, 9, 6)
(1, 1, 10, 7)
```

Without the `init_base_index` binding, the scalar reconstruction can be correct while the initial accumulator loads the wrong `Base[i]`.

This is a 4-way selection (via FinalSelector lookup), not an EC operation. Saves 2 EC rows per certificate. The selected point is consumed from the PreparedPoint copy bus using `init_base_index`:

```text
+cert_active * PreparedPoint(sig_id, cert_id, init_base_index, Ux, Uy, Uinf)
```

Because `selector_final` is consumed here, it is NOT consumed again in the chain body.

### Chain body

62 selector steps consuming selector_62 down to selector_1, plus one fixed Table[16] step (63 steps total):

```text
step 0:   selector_62     -> B_0
step 1:   selector_61     -> B_1
...
step 61:  selector_1      -> B_61
step 62:  16 (fixed)      -> B_62 = Table[16]
```

`selector_0` is NOT consumed in the chain body. It is consumed during Table[16] construction (see above).

For steps 0..61, point selection uses the Selector16Decode table to map `selector_i` to `(base_index, neg_bit)`, then applies canonical conditional negation:

```text
+cert_active * Selector16Decode(selector_i, base_index, neg_bit)
+cert_active * PreparedPoint(sig_id, cert_id, base_index, Ux, Uy_abs, Uinf)

if Uinf = 1:
    B = (0, 0, 1)
elif neg_bit = 0:
    B = (Ux, Uy_abs, 0)
elif neg_bit = 1:
    B = (Ux, p - Uy_abs, 0)
```

The negated y-coordinate is witnessed and verified: `Uy_abs + Uy_neg = p` (carry-checked). The `inf` flag gates this: infinity points stay `(0, 0, 1)`.

For step 62: `B_62 = Table[16]` is consumed from the PreparedPoint bus:

```text
+cert_active * PreparedPoint(sig_id, cert_id, 16, Ux, Uy, Uinf)
```

Total chain rows per certificate: 63 steps * 3 rows = 189 rows.

### LSB corrections

Two rows per certificate (LSB_SELECT + EC_ADD). See LSB_CORRECT row type above.

### Certificate final check: projective-affine equivalence

After LSB correction, the chain accumulator `Acc` is projective `(X_acc, Y_acc, Z_acc)`. `R3 = [3]R_signed` is affine `(x_r3, y_r3, inf_r3)` from its AFFINE_EXPORT.

**Chain invariant derivation**. The chain enforces `Acc_final = R3` where `R3 = [3]·H_signed`. The chain structure, selector decoding, MSB encoding, Table[16] correction, and LSB correction are jointly designed so this equality is equivalent to `[s1]·P + [s2_abs]·H_signed = O`. Derivation:

For each chunk `a_c ∈ {0,1,2,3}`, the signed digit is `d(a_c) = 2·a_c − 3 ∈ {−3, −1, +1, +3}`. The Selector16Decode table (16 entries) implements `selector_i = a_i + 4·b_i  →  signed_point = d(a_i)·P + d(b_i)·R` (where `R = H_signed`). For the single-bit MSBs, the FinalSelector table loads `Base[init_base_index]` directly, giving `Acc_0 = (1 + 2·s1_msb)·P + (1 + 2·s2_msb)·R` (e.g., `(s1_msb, s2_msb) = (1, 0) → Acc_0 = 3P + R`).

The chain runs 63 steps `Acc ← [4]·Acc + B_step`:

```text
step k=1..62:  B_k = d(a_{63-k})·P + d(b_{63-k})·R     (Selector16Decode)
step k=63:     B_63 = d(a_0)·P + d(b_0)·R + [3]·R     (Table[16] = Ts[selector_0] + R3)
```

Horner-expanding and re-indexing by chunk `c = 63 − k`:

```text
Acc_after_chain = 4^63·Acc_0
                + Σ_{c=0..62} 4^c · (d(a_c)·P + d(b_c)·R)
                + [3]·R
```

The LSB correction adds `C = −(1 − s1_lsb)·P − (1 − s2_lsb)·R`:

```text
Acc_final = Acc_after_chain + C
```

Collect the P-coefficient using `d(a) = 2a − 3` and `Σ_{c=0..62} 4^c = (4^63 − 1)/3`:

```text
coef_P = 4^63·(1 + 2·s1_msb) + Σ 4^c·(2·a_c − 3) − (1 − s1_lsb)
       = 4^63·(1 + 2·s1_msb) + 2·Σ a_c·4^c − (4^63 − 1) − 1 + s1_lsb
       = s1_lsb + 2·Σ a_c·4^c + 2·4^63·s1_msb
       = s1                                  (by the SELECTOR_RECON identity)
```

Identical algebra gives `coef_R = s2_abs + 3`. Therefore:

```text
Acc_final = [s1]·P + [s2_abs]·H_signed + [3]·H_signed
```

Equating to `R3 = [3]·H_signed` and using that P-256 has prime order:

```text
[s1]·P + [s2_abs]·H_signed = O
```

Combined with the FAKE_GLV_SCALAR equation `s1 + S·s2_signed ≡ 0 (mod n)`, the `s2_abs nonzero lemma`, and the canonical sign convention for `H_signed`, this implies `H = [S]·P`, completing the fake-GLV certificate.

This identity is what fixes the otherwise arbitrary-looking constants: the 16-entry Selector16Decode mapping, the four MSB entries `{5, 6, 9, 10} → init_base_index ∈ {2, 3, 6, 7}`, the LSB correction set `{O, −P, −R, −(P+R)}`, and the `+R3` offset baked into Table[16]. Any deviation breaks the identity.

**R3 must be finite**: R3 = [3]R and R is a hinted non-infinity on-curve point. Since P-256 has prime order, `[3]R = O` only if `R = O`, which is excluded by the ON_CURVE `R.inf = 0` check. Constrain:

```text
cert_active * inf_r3 = 0
```

This ensures R3 is finite on nonzero-branch rows.

**Z_acc must be nonzero**: since R3 is finite, a correct certificate produces a finite Acc. To prevent the `(0, 0, 0)` degenerate case from silently passing the cross-multiplication check (which would reduce to `0 = 0` for any R3), explicitly prove Z_acc != 0:

```text
Z_acc * Z_acc_inv = 1 mod p         (proves Z_acc != 0)
```

Then use **homogeneous** projective-affine equivalence (cross-multiplication):

```text
X_acc = x_r3 * Z_acc mod p
Y_acc = y_r3 * Z_acc mod p
```

This requires 3 Fp multiplications (`Z_acc * Z_acc_inv`, `x_r3 * Z_acc`, `y_r3 * Z_acc`). Still cheaper than Jacobian equivalence (4 muls).

May be implemented as 1-2 rows depending on Fp row width.

**s2_abs nonzero lemma**: for a nonzero-branch certificate, `s2_abs > 0`. Proof: the scalar equation is `s1 + S * s2_signed = 0 mod n`. If `s2_abs = 0`, then `s2_signed = 0`, so `s1 = 0 mod n`. But `0 < s1 < 2^128 < n`, so `s1 = 0`, contradicting `s1 > 0` (enforced by `s1_minus_one >= 0` range check). Therefore `s2_abs > 0`, which means the chain has at least one non-trivial scalar component.

## Preprocessed Trace

Include (row-deterministic, circuit-fixed):

```text
Range13(value)                     2^13 rows
Range9(value)                      2^9 rows
Range11(value)                      2^11 rows (top limb of 128-bit witnesses)
Range7(value)                     2^7 rows (values 0..127, use_count bounds)
Selector4x4(a, b, selector)       16 rows, a + 4*b = selector
Selector16Decode(selector,
  base_index, neg_bit)             16 rows, decode mapping
FinalSelector(msb1, msb2,
  selector_final, init_base_index) 4 rows (extended with init_base_index)
SignedCarryRange(value)             sized per carry bound analysis
G, [2]G, [3]G coordinates         constants
p, n, a, b constants              constants
row-type one-hot selectors         fixed per row position
boundary indicators                fixed per segment structure
sig_id(row)                        fixed per row position
cert_id(row)                       fixed per row position
step_id(row)                       fixed per row position
```

Do not include: public inputs, public key, hints, prepared table points, selectors, accumulators, carries, multiplicity columns, `cert_active`/`cert_zero_active` (these are dynamic witnesses).

## Relation Contracts

Sign convention: providers yield with **negative** multiplicity, consumers use with **positive**. This matches the stwo logup convention where the global sum must be zero.

```text
PublicEcdsaInstance(sig_id, z[20], r[20], s[20], pub_x[20], pub_y[20][, v])
  Provider: PublicData, -1 in initial_logup_sum       (yield: negative)
  Consumer: EcdsaVm PUBLIC_BIND row, +sig_active       (use: positive)
  Note: sig_id is preprocessed and part of the relation key, so public
        inputs are bound as an ordered batch. Duplicate public tuples are valid
        when they occur at different sig_id values.

Range13(value)
  Provider: Range13 component, -multiplicity (witness column)
  Consumer: every untrusted 13-bit limb, +enabler (or +cert_active for nonzero-only)

Range9(value)
  Provider: Range9 component, -multiplicity (witness column)
  Consumer: z_limb[19] in PUBLIC_BIND, +sig_active

Range11(value)
  Provider: Range11 component, -multiplicity (witness column)
  Consumer: top limb q[9] of 128-bit quotient in FAKE_GLV_SCALAR, +cert_active

Selector4x4(a, b, selector)
  Provider: Selector4x4 component, -multiplicity (witness column)
  Consumer: SELECTOR_RECON rows, +cert_active

Selector16Decode(selector, base_index, neg_bit)
  Provider: Selector16Decode component, -multiplicity (witness column)
  Consumer: chain ADD rows and Table[16] construction, +cert_active

FinalSelector(msb1, msb2, selector_final, init_base_index)
  Provider: FinalSelector component, -multiplicity (witness column), 4 rows
  Consumer: MSB initialization (MSB_SELECT), +cert_active

SignedCarryRange(value)
  Provider: SignedCarryRange component, -multiplicity (witness column)
  Consumer: carry columns in arithmetic rows, +enabler (or +cert_active)
  Encoding: carries use centered representatives in M31. For a bound C with
            C < 2^30, the preprocessed table contains every integer
            c in [-C, C] encoded as:
                enc(c) = c              if c >= 0
                enc(c) = M31_MOD + c    if c < 0
            Each arithmetic row interprets the field element through this
            unique centered encoding. The concrete C is per equation family
            and comes from the machine-checked headroom artifact.

PreparedPoint(sig_id, cert_id, table_index, x[20], y[20], inf)
  Provider: AFFINE_EXPORT rows, -use_count (dynamic witness multiplicity,
            range-bounded: 0 <= use_count <= 127 via Range7 lookup,
            logical max 65 for Base[i]; use_count = 1 for Table[16])
  Consumer: chain ADD rows (+cert_active), MSB init (+cert_active),
            Table[16] construction (+cert_active),
            LSB correction Base[2] use (+lsb00_active, conditional on (s1_lsb,s2_lsb)=(0,0))
  Note: sig_id and cert_id are preprocessed columns, preventing
        cross-signature/cross-certificate table reuse.
        Range7 enforces 0..127, not 0..65. The logical max 65
        is guaranteed by logup balance (at most 65 consumers exist
        per base index). Range7 prevents field-valued multiplicities
        but does not enforce the tight 65 bound directly.

Range7(value)
  Provider: Range7 component, -multiplicity (witness column), 128 rows (0..127)
  Consumer: AFFINE_EXPORT use_count columns, +cert_active
  Note: physical table has 2^7 = 128 rows (values 0..127). Range7 only
        prevents field-valued multiplicities. A malicious use_count = 100
        would pass Range7 but fail PreparedPoint logup balance (only
        65 consumer sites exist). The 0..65 effective bound comes from
        the fixed number of consumer sites, not from the table.
```

Internal EcdsaVm constraints (scalar setup, EC formulas, chain transitions, state loads, projective equivalence) use polynomial constraints, not logup relations.

Pair all Range13 logup fractions via `finalize_logup_in_pairs` to halve interaction columns. Numerator degree is 1 (enabler or cert_active), so paired degree = 2, well under D <= 4.

## Degree Worksheet

Target: `D <= 4`.

```text
enabler boolean:                         degree 2
cert_active constraint (enabler*snz):    degree 2, gated by row-type -> 2
branch flag sum (sz + snz = enabler):    degree 1
branch flag boolean (sz*(sz-1)):         degree 2
row-type selector (preprocessed):        degree 0 (known constant)
boolean constraint b*(1-b):              degree 2
selector one-hot flag * coordinate:      degree 2, gated -> 3
8-way mux (flag * base_coord):           degree 2, gated -> 3
canonical negation (y + y_neg check):    degree 1, gated -> 2
inf-gated conditional (inf * coord):     degree 2, gated -> 3
Uinf-conditional (Uinf * limb):          degree 2, gated -> 3
state_is_inf * Z_limb[i]:               degree 2, gated -> 3
scalar limb multiplication (a_i * b_j):  degree 2, gated -> 3
carry propagation:                       degree 1, gated -> 2
Solinas fold + correction:               degree 2, gated -> 3
complete projective formula (RCB):       degree 2-3, gated -> 3-4
previous-row state read:                 degree 1
boundary gating:                         adds 1 degree
AFFINE_EXPORT Fp equations (X*Z_inv):    degree 2, gated -> 3
AFFINE_EXPORT Y*Y_inv (inf Y!=0):        degree 2, gated -> 3
cert equiv Z_acc*Z_acc_inv:              degree 2, gated -> 3
PreparedPoint relation numerator:        degree 1 (cert_active is a column), paired -> 2
projective-affine eq (x_r3 * Z_acc):     degree 2, gated -> 3
parity extraction (ry_lo - 2*half):      degree 1, gated -> 2
R3 finite (cert_active * inf_r3):        degree 2
disabled-row (cert_zero_active * limb):  degree 2
```

Maximum: degree 4 from gated RCB projective formulas at segment boundaries. If any formula exceeds 4, split through intermediate witness columns.

Note: row-type selectors are preprocessed (degree 0), so gating by row type does not add degree. Homogeneous projective-affine equivalence uses `x * Z` (degree 2), not Jacobian `x * Z^2` (degree 3), saving one degree level.

## Fp Arithmetic: Solinas Reduction

For base-field equations, use the Solinas identity:

```text
2^256 = 2^224 - 2^192 - 2^96 + 1 mod p
```

### Limb alignment caveat

The Solinas exponents (96, 192, 224) are not multiples of `LIMB_BITS = 13`:

```text
96  = 7 * 13 + 5
192 = 14 * 13 + 10
224 = 17 * 13 + 3
```

So the Solinas fold is not a simple limb permutation. Implement it as a precomputed signed reduction matrix:

```text
2^(13*k) mod p = sum_j coeff[k][j] * 2^(13*j)
```

for every high limb position `k >= 20`, then do a carry-normalization pass. The coefficients `coeff[k][j]` are small signed integers determined by the Solinas identity. This makes the carry-bound audit tractable: each intermediate coefficient is a known linear combination of input limbs scaled by small constants.

### Reduction equations

Each Fp equation is reduced as:

```text
raw_expression - solinas_fold(high_limbs) - result - correction * p = 0
```

With:

```text
0 <= result < p                  (canonical, via borrow witness)
correction in {0, 1, 2, 3}      (placeholder bound; exact bound per operation type)
carries are signed, bounded      (range-checked via SignedCarryRange)
```

The `correction in {0, 1, 2, 3}` is a placeholder. For full multiplication, the correction bound may be larger depending on how many fold/carry-normalization passes are used. Compute exact bounds during implementation for each operation type (mul, add, sub, curve formula, affine export).

### M31 headroom audit (BLOCKER)

The statement `20 * (2^13 - 1)^2 < 2^31` proves a single convolution coefficient fits in M31. But a carry equation contains more terms:

```text
prod_coeff[i] - qn_coeff[i] - result_limb[i] + carry[i] - B * carry[i+1]
```

where `B = 2^13`. For every bigint equation, audit:

```text
|prod_coeff[i] - qn_coeff[i] - result_limb[i] + carry[i] - B * carry[i+1]| < (M31 - 1) / 2
```

ensuring the entire integer expression cannot alias to zero in M31 while being nonzero as an integer. If the bound is tight, split the equation into smaller checked pieces or widen the carry range.

**This audit is a blocker**: no arithmetic row type (EC_DOUBLE, EC_ADD, AFFINE_EXPORT, FINAL_CHECK, certificate equivalence, FnMul, Fp Solinas, scalar equation) can be considered sound until its combined carry equation is machine-checked against M31. The RCB complete formula has large intermediate expressions; the Solinas reduction has signed coefficients from misaligned exponents; the homogeneous projective-affine equivalence has `x * Z` and `y * Z` products. Each must be individually bounded.

The audit must be a checked artifact, not a hand calculation in prose. Before
an arithmetic row type is enabled in the prover, add a deterministic test or
build-time generated table that records, for each equation family:

```text
equation_name
limb_index
coefficient_bound_before_carry
carry_bound_in
carry_bound_out
max_abs_combined_expression
signed_carry_bound_C
fits_m31_centered = max_abs_combined_expression < 2^30
```

The implementation must fail tests if any row family exceeds the centered M31
limit. The `SignedCarryRange` table for that row family must then use exactly
the audited `C` bound with the centered encoding defined in Relation Contracts.
Do not reuse one global loose carry bound unless the audit proves it remains
below `2^30` for every equation family and every limb.

For each equation type, produce a concrete bound:

```text
Equation type                 Max |combined_expr|   Direct fit?     Status
Mod add/sub limb equation     65,536                yes             usable as one equation
FnMul (256x256)               5,368,045,569         no              split required
Scalar eq (256x128)           2,482,700,288         no              split required
Fp Solinas mul                pending               pending         formula not implemented
RCB Algorithm 6 (DOUBLE)      pending               pending         formula not implemented
RCB Algorithm 5 (ADD)         pending               pending         formula not implemented
AFFINE_EXPORT (X*Z_inv)       pending               pending         depends on Fp mul split
Cert equivalence (x*Z)        pending               pending         depends on Fp mul split
FINAL_CHECK (X_R*Z_R_inv)     pending               pending         depends on Fp mul split
```

The concrete values above are produced by `src/headroom.rs`. They intentionally
do not bless the current generic multiplication shape: both the full 256x256
quotient multiplication and the fake-GLV 256x128 scalar equation are too wide
as a single M31 limb equation and must be split before becoming AIR rows. The
pending rows must be filled when their concrete formulas are implemented. If any
entry exceeds `(2^31 - 2) / 2 = 2^30 - 1`, split the equation.

**Warning**: All large-limb equalities (scalar equations, Fp equations, final comparison, projective equivalence) must be enforced as integer equations with explicit carry propagation. A limb-by-limb equality without carries only proves equality mod `2^13` per limb, not as integers. Every `A - B = 0` over 20+ limbs needs a carry chain.

## Fn Arithmetic: Generic Quotient

For scalar-field equations (`s*u1 = z_red`, `s*u2 = r`):

```text
A * B - Q * n - C = 0
0 <= A, B, C < n
0 <= Q
```

Only 2 full FnMul rows per signature. Generic quotient is acceptable since this is not the bottleneck.

For the fake-GLV scalar equation (256-by-128 small-mul):

```text
S[20] * s2_abs[10] + sign * s1[10] - q[10] * n[20] = 0
```

The product `S * s2_abs` has at most 30 limb positions (20 + 10 - 1 = 29). The quotient `q` is non-negative and `q < 2^128` (10 range-checked limbs, upper positions zero). This is roughly half the cost of a full 256x256 FnMul.

## Soundness Invariants

The verifier must reject if any of the following fails:

```text
Public inputs are bound exactly once via PublicEcdsaInstance(sig_id, ...)
  (provider: -1 in initial_logup_sum; consumer: +sig_active in PUBLIC_BIND;
   sig_id is part of the relation key for ordered batches)
z < 2^256 (limb[19] < 2^9 via Range9)
z_red is the canonical reduction of z modulo n
  (integer equation z - z_red - z_ge_n*n = 0 with carries)
r and s are in [1, n-1]
  (r-1 >= 0, s-1 >= 0, r < n, s < n via borrow witnesses)
pub_x < p, pub_y < p, Pub.inf = 0
s*u1 = z_red mod n and s*u2 = r mod n
Pub is on the P-256 curve
Every row in a certificate copies scalar_is_zero/scalar_is_nonzero from that
  certificate's CERT_BIND row; branch flags are not row-local choices
Each nonzero fake-GLV branch has 0 < s1, with s1_minus_one range-checked
  (implies s2_abs > 0 via scalar equation — see s2_abs nonzero lemma)
Each nonzero fake-GLV scalar equation holds as an integer equation
  with q >= 0, q < 2^128 range-checked
Each nonzero fake-GLV selector stream reconstructs s1 and s2_abs exactly
Each selector value is decoded to (base_index, neg_bit) via Selector16Decode
Each prepared table entry is projective-to-affine exported via AFFINE_EXPORT
  using homogeneous affine recovery: x = X * Z_inv, y = Y * Z_inv
PreparedPoint copy-bus is balanced per (sig_id, cert_id, table_index):
  provider use_count equals total consumer count
Each selected chain point matches (base_index, neg_bit) from its selector
Chain transitions use RCB complete projective formulas:
  EC_DOUBLE: Algorithm 6 (exception-free doubling)
  EC_ADD: Algorithm 5 (complete mixed addition, Z2=1) + Uinf conditional
EC_ADD is complete for P+P, P+(-P), O+P, P+O, and generic P+Q
EC_DOUBLE handles DOUBLE(O) correctly — must produce valid projective
  infinity (Z=0, Y!=0), never (0,0,0)
(0,0,0) is forbidden as a projective point — not in P^2
Each nonzero fake-GLV final accumulator equals R3 via:
  Z_acc * Z_acc_inv = 1 mod p (proves Acc is finite, prevents (0,0,0) bypass)
  X_acc = x_r3 * Z_acc mod p
  Y_acc = y_r3 * Z_acc mod p
  (homogeneous cross-multiplication, not Jacobian or raw coordinate comparison)
R3 is finite: cert_active * inf_r3 = 0 (enforced at certificate final check)
H1, H2 bound via CERT_BIND rows (always present, both branches)
  nonzero: H.inf = 0, H on curve (ON_CURVE check via cert_active)
  zero: S = 0, H.inf = 1, H.x = 0, H.y = 0
  final H1+H2 loads from CERT_BIND, not ON_CURVE
R = H1 + H2 via complete projective addition
R is not infinity: Z_R * Z_R_inv = 1 mod p (no separate inf flag)
x(R) = X_R * Z_R_inv mod p (homogeneous, not X_R * Z_R_inv^2)
x(R) mod n = r as an integer equation with carries
All limbs, carries, selectors, and booleans are range-constrained
All padding rows emit zero to all logup relations (gated by enabler)
Zero-branch disabled rows have canonical zero values per row family,
  constrained by cert_zero_active (not just "prover fills zeros")
Affine infinity canonicalized: inf=1 => x=0, y=0
Projective infinity: X=0, Z=0, Y!=0 (canonical load: (0,1,0))
  AFFINE_EXPORT: state_is_inf=1 proves Z=0, X=0, Y!=0 (via Y*Y_inv=1)
  AFFINE_EXPORT: state_is_inf=0 proves Z!=0 (via Z*Z_inv=1)
Point negation uses canonical p-y, not field arithmetic on limbs
Row-type selectors are preprocessed (not malleable by prover)
CERT_BIND is included in the preprocessed row-type selector schedule
sig_id, cert_id, step_id are preprocessed (not malleable by prover)
sig_active, cert_active, cert_zero_active are materialized witnesses,
  not inline products; constrained by their defining equations
MSB init uses init_base_index from FinalSelector (not just selector_final)
PreparedPoint use_count is range-bounded (0..127 via Range7)
  Logical max 65 guaranteed by logup balance (consumer count)
use_count = 0 explicitly constrained on inactive rows (not just logup)
R3 dataflow uses fixed-schedule offsets from its AFFINE_EXPORT row
H1/H2 dataflow uses fixed-schedule offsets from their CERT_BIND rows
  (H1/H2 are hinted witness points, not AFFINE_EXPORT outputs)
LSB Base[2] consumption gated by lsb00_active, not just cert_active
128-bit quotient q bounded by Range11 on top limb q[9], not just Range13
Full FnMul quotient Q bounded by Q < n via borrow witness
M31 headroom: every bigint equation audited for non-aliasing in M31
  (blocker — must be machine-checked before any arithmetic row is sound)
SignedCarryRange uses the audited centered M31 encoding and per-family bound
```

## Negative Tests

```text
z = 2^256                              -> Range9 failure on z_limb[19]
z_red mutated                          -> digest reduction failure
r = 0                                  -> r >= 1 range failure
s = 0                                  -> s >= 1 range failure
r = n                                  -> r < n borrow witness failure
pub_x >= p or pub_y >= p               -> canonical field range failure
pub_y mutated (off-curve)              -> ON_CURVE failure
s*u1 != z_red                          -> SCALAR_SETUP FnMul failure
s*u2 != r                              -> SCALAR_SETUP FnMul failure
s1 mutated by 1                        -> scalar equation or selector failure
s2_sign_bit flipped                    -> scalar equation or chain failure
s2_abs = 0 forced                      -> s1_minus_one check implies s1>0 which
                                          implies s2_abs>0 via scalar equation
S = 0 with nonzero branch              -> s1>0 makes scalar eq unsatisfiable
H1 replaced with random on-curve point -> cert final projective-eq failure
Table entry correct but chain uses
  altered copy                         -> PreparedPoint copy-bus imbalance
One selector digit mutated             -> reconstruction or chain failure
Selector flag doesn't match decode     -> Selector16Decode lookup failure
One chain accumulator coordinate
  mutated                              -> EC transition failure
Projective Acc matches R3 by raw
  coords but not affine equivalence    -> projective-affine eq failure
Final R set to O (Z_R = 0)            -> Z_R * Z_R_inv = 1 failure (no inv exists)
x_ge_n set to 2                        -> boolean constraint failure
x(R) mutated while preserving limbs    -> final comparison failure
FINAL_CHECK uses X_R * Z_R_inv^2
  instead of X_R * Z_R_inv            -> wrong affine x, comparison failure
2^13 in any limb                       -> Range13 lookup failure
2^9 in z_limb[19]                      -> Range9 lookup failure
Relation emitted on padding row        -> logup imbalance
Public tuple with wrong sig_id          -> PublicEcdsaInstance logup imbalance
Duplicate public tuple at two sig_ids   -> valid when PublicData emits both
                                          ordered tuples with distinct sig_id
Point negation emits (x, p) instead
  of (0, 0, 1) for infinity           -> infinity canonicalization failure
Mixed-add with infinity operand
  treated as Z=1                       -> EC_ADD Uinf-conditional failure
Unconstrained chain row in zero branch
  emits PreparedPoint                  -> cert_active gating failure
EC_ADD with state_prev == operand
  (doubling case)                      -> RCB complete formula handles correctly
EC_ADD with state_prev == -operand
  (result is infinity)                 -> RCB complete formula produces Z_out=0
EC_DOUBLE with O input: verify
  output is valid projective O         -> Algorithm 6 must produce (0,?,0) with Y!=0
  If Algorithm 6 produces (0,0,0)      -> MUST add explicit conditional or use Alg 4
AFFINE_EXPORT: state_is_inf = 0 but
  Z = 0 (lying about finiteness)      -> Z * Z_inv = 1 fails (no inverse)
AFFINE_EXPORT: state_is_inf = 1 but
  Z != 0 (lying about infinity)       -> state_is_inf * Z_limb[i] = 0 fails
AFFINE_EXPORT: state_is_inf = 1,
  Z = 0, X = 0, but Y = 0 too        -> Y * Y_inv = 1 fails (forbidden (0,0,0))
Cert equivalence: Acc = (0,0,0) with
  finite R3                            -> Z_acc * Z_acc_inv = 1 fails
Cert equivalence: adversary forges
  Acc with Z_acc = 0, passes cross-mul -> Z_acc_inv check rejects
H1 loaded from ON_CURVE instead of
  CERT_BIND when u1 = 0 (zero branch)  -> no active ON_CURVE row, must use CERT_BIND
CERT_BIND: zero branch H has
  inf = 0 (lying about H = O)         -> scalar_is_zero * (H_inf - 1) = 0 fails
Wrong MSB base index: selector_final
  correct but Acc0 loads wrong Base[i] -> FinalSelector init_base_index mismatch
PreparedPoint wrong sig/cert: correct
  coords but wrong sig_id or cert_id  -> PreparedPoint bus imbalance
PreparedPoint use_count > 127          -> Range7 lookup failure
PreparedPoint use_count_16 != 1        -> logup imbalance
cert_active gating bug:
  zero branch emits selector or
  PreparedPoint relation               -> logup imbalance or constraint failure
Branch flag mismatch:
  CERT_BIND says zero branch but a
  chain row uses nonzero branch flags   -> fixed-schedule branch copy failure
  CERT_BIND says nonzero branch but a
  prep row sets cert_active = 0         -> cert_active defining/copy failure
Disabled EC row in zero branch has
  nonzero witness values               -> cert_zero_active * limb constraints fail
R3 dataflow mutation: correct R3
  export but final proj-eq uses
  altered R3 coordinates               -> fixed-offset constraint failure
H1/H2 dataflow mutation: certificate
  proves one H but final addition
  loads different H                    -> fixed-offset constraint failure
R3 is infinity (inf_r3 = 1)           -> cert_active * inf_r3 = 0 failure
q top limb q[9] = 2^11 (overflow)     -> Range11 lookup failure
q[9] = 2^13 - 1 with other limbs
  making q >= 2^128                    -> Range11 lookup failure on q[9]
FnMul quotient Q = n                   -> Q < n borrow witness failure
LSB (s1_lsb,s2_lsb) = (1,0) but
  Base[2] consumed anyway             -> lsb00_active prevents emission
use_count = 1 on inactive AFFINE_EXPORT
  row (zero branch)                    -> (1-cert_active)*use_count failure
Parity extraction: odd_y = 2           -> odd_y boolean constraint failure
Parity extraction: ry_lo_half forged   -> ry_lo - 2*ry_lo_half != {0,1}

Must-fail edge cases:
x_ge_n = 1 when r + n >= p            -> must fail: x(R) cannot exceed p
Try zero branch for H2                 -> must fail: u2 = r * s^(-1) mod n,
                                          and 1<=r<n, 1<=s<n, so u2 != 0
PreparedPoint use_count mismatch       -> logup imbalance

Valid edge cases that must PASS:
S = 1                                  -> table entries hit O, valid
S = n-1                                -> same pattern, valid
S = 3                                  -> some entries may hit O
S = n-3                                -> same
S = 3^(-1) mod n                       -> T4-related entries
S = -3^(-1) mod n                      -> T3-related entries
u1 = 0 (z_red = 0)                    -> valid zero H1 branch via CERT_BIND
x(R) = r + n (valid reduction)         -> x_ge_n = 1 path
DOUBLE(O) followed by ADD             -> chain handles projective O correctly
AFFINE_EXPORT of infinity point        -> state_is_inf=1, Y!=0 check passes
Cert equivalence with finite Acc       -> Z_acc_inv exists, cross-mul passes
```

## Row Count Estimate

Per signature (packed shape):

```text
1-3  PUBLIC_BIND + INPUT_VALIDATE
2    SCALAR_SETUP (s*u1=z_red, s*u2=r)
2    FAKE_GLV_SCALAR (one per cert, 256x128 signed mul)
16   SELECTOR_RECON (8 per cert)
2    CERT_BIND (one per cert, binds H + zero/nonzero branch)
3-9  ON_CURVE (Pub + H1 + H2, may split for Fp width)
~10  STATE_LOAD (table prep jumps, cert boundaries, Table[16] load)
11   EC prep cert 0 (G specialized, EC ops only)
13   EC prep cert 1 (Pub, EC ops only)
20   AFFINE_EXPORT (10 per cert: Base[0..7] + R3 + Table[16])
2    MSB_SELECT for MSB init (one per cert)
378  chain EC rows (63 steps * 3 rows * 2 certs)
4    LSB correction (2 per cert: LSB_SELECT + EC_ADD)
2-4  cert final projective-affine equivalence (1-2 Fp rows per cert;
       homogeneous needs 3 muls: Z_acc_inv + 2 cross-muls)
1    EC_ADD for H1+H2
1-3  FINAL_CHECK (Z_inv, affine x = X*Z_inv, comparison; may split)
---
~480-520 active rows per signature before final Fp row packing
```

Row budget with splitting scenarios:

```text
Best case (1-row AFFINE_EXPORT, 1-row cert-eq):  ~480-490 rows
2-row AFFINE_EXPORT:                               ~500-510 rows  (+20)
2-row AFFINE_EXPORT + split EC rows:               ~510-540 rows  (+10-30 more)
```

The homogeneous coordinate model saves degree and intermediate work compared to Jacobian: AFFINE_EXPORT and FINAL_CHECK avoid `Z^2`/`Z^3` denominator construction, certificate equivalence uses linear-in-`Z` cross-products, and all boundary equations remain degree-2 before gating. Row savings depend on the final packed Fp row shape and must be measured after the M31 headroom audit.

Target: `log_size = 9` (512 rows) only after packing proves the row count fits.
Fallback: `log_size = 10` (1024 rows) if splitting exceeds 512 rows.

Padding to `2^9 = 512`. Utilization at best case: approximately `480/512 = 94%`.

If implementation pushes above 512, the next natural log size is `2^10 = 1024` with ~50% utilization. Not catastrophic if column count is low, but worth optimizing the row layout to stay in 512. The implementation should have a fallback schedule for `2^10` rows.

Estimated sizing:

```text
dynamic committed columns:         ~350-500 (with PreparedPoint copy bus,
                                     sig_id/cert_id/step_id preprocessed)
interaction columns:               depends on relation count and batching
active rows per signature:         ~480-520
log_size for 1 signature:          9 (target), 10 (fallback)
global log with Range13/logup:     ~14-15
```

## Implementation Order

```text
1.  Implement limb range helpers and canonical < n, < p comparisons.
    Include Range13, Range9, Range11, and Range7 lookup providers.
2.  Implement full FnMul (scalar setup) and digest reduction.
    Bound quotient Q < n via borrow witness.
3.  Implement Fp Solinas arithmetic with signed reduction matrix
    and carry analysis. Machine-check M31 headroom per equation type
    (see M31 headroom audit BLOCKER). Fill the headroom table and derive
    the centered SignedCarryRange bound for each equation family.
4.  Implement RCB exception-free EC_DOUBLE (Algorithm 6) and
    complete mixed EC_ADD (Algorithm 5) for short Weierstrass a=-3.
    EC_ADD handles all 5 cases via RCB + Uinf-conditional.
    Verify DOUBLE(O) output by substituting (0,1,0) into Algorithm 6:
    confirm Z_out = 0 and Y_out != 0 (not the forbidden (0,0,0)).
    Include canonical point negation helper (p - y with inf gating).
    Add negative tests for P+P, P+(-P), O+P, DOUBLE(O) inputs.
    No inf_out flag — pure homogeneous projective (X, Y, Z).
5.  Implement AFFINE_EXPORT (homogeneous projective -> canonical affine).
    Uses state_is_inf witness: inf=0 proves Z!=0 via inverse,
    inf=1 proves Z=0 via per-limb constraints AND X_limb[i]=0 AND
    Y*Y_inv = 1 mod p (proves Y!=0, preventing forbidden (0,0,0)).
    Affine recovery: x = X*Z_inv, y = Y*Z_inv (NOT Jacobian).
    Include use_count range bound via Range7.
    Constrain use_count = 0 on inactive rows via (1-cert_active)*use_count.
6.  Implement CERT_BIND row type (binds H point + zero/nonzero branch).
    Always present for both branches. Defines scalar_is_zero, H coords,
    h_inf, and receives S via fixed-schedule offset. Constraints:
    branch flags are boolean and sum to enabler; every row in the certificate
    copies these flags from CERT_BIND; zero branch forces S = 0, H_inf = 1,
    H_x = 0, and H_y = 0; nonzero branch forces H_inf = 0 and canonical H.
    H1/H2 final addition loads from CERT_BIND rows, not ON_CURVE.
7.  Implement ON_CURVE check (gated by cert_active, not cert_zero_active).
    H coordinates must match corresponding CERT_BIND row.
8.  Implement fake-GLV scalar equation (256x128 signed small-mul).
    Bound q[9] < 2^11 via Range11. Constrain q[10..19] = 0.
9.  Implement selector reconstruction (packed rows).
    Add Selector4x4, Selector16Decode, FinalSelector
    (extended with init_base_index) tables.
10. Implement prepared table construction with STATE_LOAD rows
    (including affine-to-projective conversion with (0,1,0) for infinity)
    and AFFINE_EXPORT after each Base[i], R3, Table[16].
    (cert 1 first, then specialize cert 0 with preprocessed G constants).
    Include Table[16] construction with full decode-fetch-negate-add pipeline.
    R3 connects via fixed-schedule offset, NOT PreparedPoint bus.
11. Implement PreparedPoint copy-bus relation with counted, range-bounded
    multiplicities. LSB Base[2] uses lsb00_active, not cert_active.
12. Implement chain as individual DOUBLE, DOUBLE, ADD rows
    with 63 steps per cert (62 selector steps + 1 fixed Table[16]).
    Chain ADD rows perform operand selection inline (decode, fetch, negate).
    Wire Selector16Decode and PreparedPoint consumption in ADD rows.
    Test against Garaga-generated fake-GLV hints.
13. Implement MSB_SELECT (with init_base_index from FinalSelector)
    and LSB correction (LSB_SELECT + EC_ADD split) with conditional
    lsb00_active gating, canonical negation, and infinity handling.
14. Implement certificate final check (homogeneous projective-affine
    cross-multiplication: X_acc = x_r3*Z_acc, Y_acc = y_r3*Z_acc).
    Add Z_acc_inv witness proving Z_acc != 0 (Acc is finite).
    Add R3 finite constraint: cert_active * inf_r3 = 0.
15. Wire previous-row transitions, boundary indicators,
    preprocessed row-type selectors, preprocessed sig_id/cert_id/step_id,
    and materialized sig_active/cert_active/cert_zero_active/lsb00_active
    columns with their defining constraints. Include `is_cert_bind` in the
    fixed row-type schedule and enforce certificate-wide branch flag copies.
16. Wire PUBLIC_BIND (expanded with all input validation) and FINAL_CHECK
    (Z_R inverse for R!=O, homogeneous affine x = X_R*Z_R_inv, comparison).
    Include exact parity extraction for recovery_id if needed.
    H1/H2 loaded via fixed-schedule offsets from their CERT_BIND rows.
17. Add public data binding and initial_logup_sum.
    Provider: -1 * PublicEcdsaInstance(sig_id, ...). Consumer: +sig_active.
    `sig_id` is part of the relation key so duplicate public tuples at
    different positions are valid and unambiguous.
18. Implement zero-scalar branch with cert_active/cert_zero_active gating,
    explicit disabled-row constraints per row family (cert_zero_active * limb = 0),
    and explicit use_count = 0 constraints.
19. Run all negative tests and edge-case completeness tests.
    Include: RCB EC_ADD P+P and P+(-P), DOUBLE(O), EC_ADD with (0,0,0),
    AFFINE_EXPORT state_is_inf soundness (both directions),
    AFFINE_EXPORT infinity (0,0,0) rejection (Y!=0),
    cert equivalence Z_acc=0 bypass, CERT_BIND zero-branch lies,
    Algorithm 6 DOUBLE(O) output validation,
    MSB base-index mismatch, PreparedPoint use_count bounds and inactive=0,
    lsb00_active conditional, R3/H dataflow mutations, cert_active gating,
    disabled-row constraint violations, R3 infinity,
    q top-limb overflow, FnMul Q >= n, parity extraction attacks.
20. Benchmark and profile. Consider QuadAdd batching only after
    baseline is correct and measured.
```

Do not batch chain steps into wide rows (QuadAdd9) until the baseline DOUBLE/DOUBLE/ADD implementation passes all tests and is profiled.

## Implementation Notes for This Repo

- Keep `LIMB_BITS = 13` and `N_LIMBS = 20`; this is already the right representation for M31 multiplication headroom.
- Replace the placeholder `MulModEval` with separate `FnMulEval` (generic quotient for scalar field) and `FpSolinasEval` (Solinas reduction for base field). The current generic `MulModWitness` shape is useful for tests but should not be the hot base-field AIR path.
- Add a `PublicData` layer before proving APIs are finalized. `EcdsaProof` currently stores public fields but has no binding mechanism.
- Use RCB Algorithm 6 (exception-free doubling) and Algorithm 5 (complete mixed addition) for all EC operations. Both use homogeneous projective coordinates `(X, Y, Z)` with affine recovery `x = X/Z, y = Y/Z`. Do not mix Jacobian formulas. Verify that Algorithm 6 applied to `(0,1,0)` does not produce `(0,0,0)`.
- Verify RCB formula correctness for degenerate valid inputs such as `(0, 1, 0)`, and verify that `(0, 0, 0)` is either unreachable or explicitly rejected before integration.
- Gate all nonzero-branch logic by `cert_active`, not inline `enabler * scalar_is_nonzero`.

## Deterministic Fallback: Shamir/Horner

If hints are unavailable, a deterministic double-scalar multiplication serves as a fallback. Use Horner order from the most significant base-32 window:

```text
A = O
for i in (51 down to 0):
    repeat 5 times: A = double(A)
    A = A + [u1_i]G
    A = A + [u2_i]Q
```

`G` digit points are fixed preprocessed lookups. `Q` digit points are proved once by `QWindowTable` and then used by the scalar-mul plan.

Digit reconstruction must prove:

```text
u = sum_{i=0}^{51} digit_i * 32^i
```

with each digit in `[0, 31]` and the high unused bits constrained to zero because `u1, u2 < n < 2^256`.

This costs ~394 EC transition rows per signature (260 doublings + 104 mixed-add slots + overhead). Treat as a benchmark baseline for the fake-GLV design.

## Garaga Cross-Check

Garaga's ECDSA verifier (`src/src/signatures/ecdsa.cairo`) does the following:

- checks `r != 0`, `1 <= s < n`
- checks the public key is on curve and not infinity
- computes `s_inv`, `u1 = z*s_inv mod n`, `u2 = r*s_inv mod n`
- computes `R' = msm_g1([G, public_key], [u1, u2], curve_id, msm_hint)`
- checks `R'` is nonzero and `R'.x mod n == r`
- additionally checks `is_even(R.y) != v`

For P-256 (`curve_id = 3`), `msm_g1` uses `msm_fake_glv`, not the GLV endomorphism route. The off-chain calldata builder generates one fake-GLV hint per scalar multiplication: `(Q, s1, s2)`, where `Q = [scalar]P`, and the Cairo code verifies `s1 + scalar*s2 = 0 mod n` plus a short EC relation.

This AIR adopts Garaga's fake-GLV certificate as the primary scalar-multiplication proof. The Shamir/Horner fallback above remains as a no-hints alternative or benchmark baseline.
