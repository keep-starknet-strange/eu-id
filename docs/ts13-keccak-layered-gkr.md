# TS13 layered Keccak prototype

Status: independently reviewed; accepted as sound with conditions

A-015-review accepts this committed-nibble design as sound. It reports no
critical or high finding. Final campaign acceptance still requires conditions
F-1 through F-3, a new source-bound artifact, the full release matrix, and the
three-phone run. A-016 requires the candidate to preserve or improve the live
whole-system algebraic bound under the same accounting convention.

This design replaces the removed Keccak round carrier. It does not change the
TS13 identity theorem, ML-DSA-65, the public statement, the PCS settings, the
STWO revision, local proving, or the product API.

The privacy claim stays:

```text
public-input unlinkable; transcript zero knowledge pending
```

STWO is not zero knowledge. This work does not add transcript masking.

## 1. Fixed scope

The implementation MUST keep these properties:

- `proveIdentity` and `verifyIdentity` are the only product proof functions.
- The proof verifies all 261 required Keccak-f[1600] permutations.
- The proof uses all 24 FIPS 202 rounds and the correct Iota constant in each
  round.
- The proof binds each permutation input and output to the same sponge row.
- The proof keeps the fixed, credential-independent envelope.
- The proof does not add a public or credential-stable identifier.
- The proof keeps the pinned STWO revision and the selected PCS parameters.

Use one layered protocol for every `KeccakService` shape. Derive the number of
permutation variables `p_log` from the public `JobList::log_size()`. Smaller
standalone service tests use this same prover, verifier, transcript, codec,
and pair of tie-backs. Do not retain the old carrier as a fallback. The TS13
product artifact separately requires `p_log = 9`.

The replacement mass MUST not exceed 320,000 committed cells. The candidate
uses 212,992 cells. A-016 retires the complete-Keccak 1,200 ms sub-gate because
the timing wire cannot measure it. Performance acceptance requires one full
cold `proveIdentity` call below 2,000 ms on each gate phone. Keep the matching
desktop phase record.

## 2. Authoritative row order

The permutation coordinate `p` has nine bits. It is the physical MLE storage
row after the circle-index and bit-reversal transforms. It is not the logical
coset row and it is not the predicate `p < 261`.

The existing `is_active` schedule column defines the 261 active storage rows.
The existing `perm_id` schedule column defines the permutation identifier at
each storage row. All GKR maps use these two canonical columns. A map returns
zero when `is_active` is zero.

The prover converts a logical sponge row to this storage order with the same
`col_eval` path that commits the sponge columns. The input and output source
columns therefore use the same `p` coordinate.

## 3. Committed input source

Add 400 base columns to the vertical sponge. Append them after the current
base columns. Use this order:

```text
lo(byte 0), hi(byte 0), lo(byte 1), hi(byte 1), ...,
lo(byte 199), hi(byte 199)
```

Store the exact 200-byte pre-permutation state in `RowData`. For a
capacity-allocated row that does not absorb, this state is all zero even
though `prev_post` still contains the prior real state. This matches the live
canonical `Keccak-f(0)` row. Derive all input nibbles and the negative input
tuple from this exact stored state.

For exact pre-permutation input byte `j`, commit:

```text
lo_j = spread(input_j & 0x0f)
hi_j = spread(input_j >> 4)
```

Recompose the state limb as:

```text
input_spread_j = lo_j + 256 * hi_j
```

Use nibble slot `n = 2*j + h`, where `h = 0` selects `lo` and `h = 1`
selects `hi`. Slots 400 through 511 are virtual zero slots. Constrain every
committed nibble to zero when the existing `is_active` column is zero.

The vertical sponge emits one positive computed-input entry and one negative
committed-input entry. Both use the existing permutation ID and the same
recomposed `input_spread` state. This gives one positive and one negative input
tuple for each row.

Use the canonical tuple `(permutation_id, state[200])`. Do not retain a
constant direction or state tag.

The removed carrier state entries are not retained. The layered proof binds
the input columns directly to the existing `post[200]` output columns.

## 4. Circuit domains

Use these Boolean domains:

```text
A_r(p9, lane5, z6)  input and output state bits
B_r(p9, lane5, z6)  state after Theta, Rho, and Pi
C_r(p9, x3, z6)     column parity bits
```

`lane = x + 5*y` for live lanes. Lanes 25 through 31 are zero. Values with
`x >= 5` in `C` are zero. Values on an inactive permutation row are zero.

The bit coordinate `z` is the little-endian bit position in a 64-bit Keccak
lane. The generation input does not list `RHO_OFFSETS`, `IOTA_RC`, the
24-round control flow, or the gate degrees as separate constants. The circuit
identity binds these values through the soundness-source-tree digest, which
covers `crates/stwo-keccak`. The product payload gate separately requires
`p_log = 9`, 8,894 QM31 values, and 142,304 bytes. It rejects noncanonical
limbs and trailing bytes.

For Boolean inputs, use this fixed parity polynomial:

```text
XOR_k(v_0,...,v_(k-1)) = (1 - product_i(1 - 2*v_i)) / 2
```

### 4.1 Parity

For live coordinates:

```text
C_r[p,x,z] = XOR5_y A_r[p,x+5*y,z]
```

The gate reads five `A_r` values. Its domain has 18 variables. The gate and
the incoming functional have degree at most six in each variable. Its
sumcheck coefficient is `18*6 = 108`.

### 4.2 Theta, Rho, and Pi

For target coordinates `(x_t,y_t,z_t)`, define:

```text
x_s = (x_t + 3*y_t) mod 5
y_s = x_t
z_s = (z_t - RHO_OFFSETS[x_s][y_s]) mod 64
```

Then:

```text
B_r[p,x_t+5*y_t,z_t] = XOR3(
    A_r[p,x_s+5*y_s,z_s],
    C_r[p,(x_s-1) mod 5,z_s],
    C_r[p,(x_s+1) mod 5,(z_s-1) mod 64]
)
```

This is the inverse read map for the FIPS 202 Rho and Pi steps. The gate reads
one `A_r` value and two `C_r` values. Its domain has 20 variables. The gate
and incoming functional have degree at most four in each variable. Its
sumcheck coefficient is `20*4 = 80`.

### 4.3 Chi and Iota

For live `(x,y,z)`, set:

```text
t = (1 - B_r[x+1,y,z]) * B_r[x+2,y,z]
chi = B_r[x,y,z] + t - 2*B_r[x,y,z]*t
q = is_active(p) * is_lane_zero(x,y) * ((IOTA_RC[r] >> z) & 1)
A_(r+1)[x,y,z] = chi + q - 2*chi*q
```

All `x` additions are modulo five. `q` is zero outside lane zero and outside
active rows. The gate reads three `B_r` values. Its domain has 20 variables.
The gate and incoming functional have degree at most five in each variable.
Its sumcheck coefficient is `20*5 = 100`.

The three gates contribute `288` per round and `6,912` for all 24 rounds.

## 5. Carried linear functionals

A claim on a layer has this form:

```text
c_h = sum_x K_h(x) * V(x)
```

Each kernel `K_h` is fixed by prior transcript challenges and a fixed wiring
map. After all current claims are fixed, draw `alpha` and form:

```text
E(x) = sum_h alpha^h * K_h(x)
```

Run one main sumcheck for the gate with `E` as its coefficient. At the final
point, the prover sends the declared read values. Each read becomes a claim
on the next layer. Its kernel is the multilinear extension of the fixed read
matrix at the final point.

Do not treat an arbitrary lane permutation as a coordinate permutation at a
non-Boolean point. The verifier evaluates the fixed wiring kernel:

```text
W_f(omega,r) = sum_x eq(omega,x) * eq(r,f(x))
```

The permutation part factors through the 512-row active schedule. The
lane-and-bit part uses a fixed table of at most 2,048 entries. The verifier
does not enumerate a `2^20` table.

Process each round backwards:

1. Chi and Iota produce three `B_r` claims.
2. Theta, Rho, and Pi batch those three claims and produce one direct `A_r`
   claim plus two `C_r` claims.
3. Parity batches the two `C_r` claims and produces five `A_r` claims.
4. Carry the direct `A_r` claim with the five parity claims.

The first Chi layer receives one output claim. Each later Chi layer receives
six claims. The exact RLC collision coefficient is:

```text
23*(6-1) + 24*(3-1) + 24*(2-1) = 187
```

## 6. Input extraction and validity

The valid spread-nibble set is:

```text
D = {0,1,4,5,16,17,20,21,64,65,68,69,80,81,84,85}
```

Define:

```text
P(X) = product_(v in D) (X-v)
```

For bit `i` from zero through three, define the degree-15 Lagrange polynomial
that returns bit `i` on `D`:

```text
f_i(X) = sum_(v in D, bit_i(v)=1) (
    product_(u in D, u != v) (X-u)/(v-u)
)
```

The generation input does not list `D`, `P`, or the four `f_i` coefficient
arrays as separate constants. The circuit identity binds `VALID_NIBBLES` and
the deterministic `nibble_polynomials` derivation through the same
soundness-source-tree digest. The exact product payload gate stated in
section 4 also applies to this sumcheck.

The identity below holds over M31:

```text
X = f_0(X) + 4*f_1(X) + 16*f_2(X) + 64*f_3(X)
```

For nibble slot `n = 2*j+h`, bit `i`, and byte
`j = 8*lane + floor(z/8)`, use:

```text
h = floor((z mod 8)/4)
i = z mod 4
A_0[p,lane,z] = f_i(N[p,n])
```

The map is a bijection between the 2,048 padded state-bit slots and the
512 nibble slots times four bits. Dead state lanes map to virtual zero nibble
slots.

Do not commit or accept a separate bit oracle.

After the six `A_0` claims are fixed, draw the random 18-variable validity
point `tau`. Then draw one powers challenge `alpha` and combine the six
claims. For each carried kernel `K_h`, define `K_(h,i)` as the unique
18-variable MLE whose Boolean table is the restriction below:

```text
K_(h,i)(p,n) = K_h(p, pi(n,i))
E_i(p,n) = sum_(h=0..5) alpha^h * K_(h,i)(p,n)
```

`pi` is the fixed Boolean nibble-and-bit to lane-and-bit map. Do not compose
the original 20-variable MLE with an integer or lane permutation at a
non-Boolean point. The prover restricts the Boolean kernel table. The
verifier evaluates the same fixed restricted wiring kernel.

Draw a fresh challenge `lambda`. Prove this 18-variable sum by one degree-17
sumcheck:

```text
sum_(p,n) (
    sum_(i=0..3) E_i(p,n) * f_i(N[p,n])
  + lambda * eq(tau,(p,n)) * P(N[p,n])
)
```

The validity term has claimed sum zero. If any committed nibble is not in
`D`, its random evaluation is zero with probability at most `18/(q-2)`.

The functional terms have per-variable degree 16. The validity term has
per-variable degree 17. The sumcheck coefficient is `18*17 = 306`. The six
state claims plus the validity claim give RLC coefficient six. The terminal
check uses one value `N(r)`.

## 7. Output boundary

Draw a random output point with nine storage-row coordinates and eight byte
slot coordinates. Fold the existing `post[200]` columns at the byte point.
Slots 200 through 255 are virtual zero slots. Mix the claimed value.

Split the byte slot as five lane bits and three byte-in-lane bits. Map it to
the final `A_24` point. Set the three bit-in-byte coordinates, from most to
least significant, to:

```text
256/257, 16/17, 4/5
```

Then:

```text
post_mle = 21845 * A_24_mle
```

This follows from `21845 = 257*17*5` and the spread weights `4^bit`. A false
output boundary survives the random 17-variable point with probability at
most `17/(q-2)`.

## 8. Two committed-source tie-backs

Use two instances of the pinned log-9 `MleEval` component.

1. The output instance opens the fold of `post[200]` at the output row point.
2. The input instance opens the fold of the 400 nibble columns at the input
   row point from the extraction sumcheck.

Both coefficient oracles read the allocated sponge trace locations. They do
not use hard-coded global column offsets. Emit the output tie-back first and
the input tie-back second. Tree 3 contains 16 M31 columns.

The pinned component cannot accept an evaluation coordinate equal to zero or
one. Draw all local protocol challenges with a deterministic rejection loop
over `QM31 \\ {0,1}`. The prover and verifier run the same loop. Use `q-2` as
the soundness denominator.

## 9. Transcript

After tree 2 and all retained claimed sums:

1. Mix a fixed layered-Keccak protocol tag and the artifact-bound shape.
2. Draw the 17 output coordinates.
3. Mix the output source claim.
4. For rounds 23 through zero, process Chi/Iota, Theta/Rho/Pi, then Parity.
5. Draw each claim RLC only after all claims in that batch are fixed.
6. In each sumcheck round, mix the fixed-length polynomial before drawing the
   next challenge.
7. Mix every declared terminal read before drawing a challenge that uses it.
8. Draw the 18-variable nibble-validity point.
9. Draw the extraction powers challenge and `lambda`.
10. Run the 18-round extraction and validity sumcheck.
11. Mix the one terminal nibble value.
12. Build the output and input tie-back traces.
13. Commit the 16 tree-3 columns.
14. Continue the normal STARK OODS, PCS, FRI, and proof-of-work transcript.

Do not serialize a challenge or point that the transcript derives.

## 10. Fixed payload

Encode each QM31 value as four canonical, little-endian M31 limbs. Reject a
limb greater than or equal to `2^31-1`. Reject a short payload and every
trailing byte.

Read the raw payload in transcript order:

1. Read the initial output claim.
2. For rounds 23 through zero, read the 20 Chi polynomials and three Chi
   terminals, the 20 Theta polynomials and three Theta terminals, then the
   18 parity polynomials and five parity terminals.
3. Read the 18 extraction polynomials and the extraction terminal.

The aggregate count is:

| Section | QM31 values |
| --- | ---: |
| 24 Chi sumchecks, `20*6` each | 2,880 |
| 24 Chi terminal triples | 72 |
| 24 Theta sumchecks, `20*5` each | 2,400 |
| 24 Theta terminal triples | 72 |
| 24 parity sumchecks, `18*7` each | 3,024 |
| 24 parity terminal groups of five | 120 |
| Extraction sumcheck, `18*18` | 324 |
| Extraction terminal | 1 |
| Initial output claim | 1 |
| **Total** | **8,894** |

The exact payload size is 142,304 bytes. The local verifier accepts no other
shape. The generic degree-three GKR wire and decoder are deleted.

For a non-product service with public `p = p_log`, derive the expected field
count and byte count from the `JobList`:

```text
field_count(p) = 450*p + 4844
byte_count(p) = 7200*p + 77504
```

The same decoder still rejects a wrong length, a noncanonical limb, and every
trailing byte. The TS13 envelope validator accepts only the `p = 9` result.

## 11. Soundness ledger

Let `q = (2^31-1)^4`. Under the same conservative accounting used for the
removed carrier baseline, the K contribution is:

| Event | Coefficient |
| --- | ---: |
| Round sumchecks | 6,912 |
| Round functional RLCs | 187 |
| Grouped extraction and validity sumcheck | 306 |
| Extraction and validity RLC | 6 |
| Random nibble-validity point | 18 |
| Random output boundary | 17 |
| Two conservative log-9 MLE identities | 1,022 |
| **Total** | **8,468** |

Thus:

```text
epsilon_K <= 8468/(q-2)
```

The removed carrier uses `8974/q` under the same convention. The replacement
improves that coefficient by 506, before the negligible denominator change.
The `8974/q` carrier value is doc-asserted. Its supporting ledger,
`759 + 23 + 1 + 8191`, was deleted with `round_gkr.rs`. No live generator or
test independently recomputes it. Acceptance does not depend on this
comparison because both Keccak terms are smaller than the retained OODS term.

The two MLE constraints are also part of the one outer STARK composition and
OODS event. A whole-system audit MUST not count them again after it counts
that global event. The current global OODS coefficient is `2^18-1 = 262143`,
not the stale log-16 split-part value. Artifact regeneration MUST recompute
the quotient-term and relation-collision counts.

The new plain constraints have degree two. The sponge already needs
`log_size+2` for its batched LogUp constraints. The two MLE components need
`log_size+1`. The design therefore keeps composition split two.

## 12. Geometry

The prototype replacement mass is:

| Addition | Cells |
| --- | ---: |
| 400 nibble columns at log 9 | 204,800 |
| Two eight-column MLE traces at log 9 | 8,192 |
| New interaction columns | 0 |
| New preprocessed columns | 0 |
| **Total** | **212,992** |

The canonical service accepts at most 136 absorbed bytes for each SHAKE-128
job. Every TS13 SHAKE-128 job absorbs 34 bytes. SHAKE-128 still emits the full
168-byte rate for every squeeze block. The trace commits 136 columns for each
absorb byte, absorb spread, new rate, and capacity pad family. It derives the
remaining 32 absorb positions from the public padding schedule. The AIR omits
the 32 high conversion, absorb-input, and XOR entries. It also omits the
later-absorb SHAKE-128 state entry.

After removal of the old carrier, schedule table, AndNot table, and split
tables, the complete Keccak layout is:

```text
preprocessed:    16@9, 2@16, 2@8
trace:           1314@9, 1@16, 1@8
interaction:     752@9, 4@16, 4@8
post-interaction: 16@9
```

This is 1,534,720 AIR-reference cells. The physical system total is projected
at 9,156,176 cells. The replacement passes the 320,000-cell prototype gate.
A-013 supersedes the earlier 1.5-million complete-Keccak gate for the AIR
track. A-015 suspends the committed-bit route and keeps the engine route open
for future work. A-015-review accepts this candidate as sound, subject to the
three recorded completion conditions.

A-016 requires one cold full-proof run on all three gate phones. Keep the
matching desktop phase record in the same evidence set. Complete the review
conditions and final-hash evidence before starting another cryptographic path.
If one phone misses the 2,000 ms gate, use a new accepted lever or obtain an
explicit gate change.

## 13. Required checks

The canonical implementation has one `layered_gkr` path. It does not contain
the old carrier, round GKR, round schedule, round trace, or generic wire. It
keeps only the XOR and conversion tables used by this protocol.

At minimum, release tests MUST cover:

- every FIPS lane, Rho, Pi, bit, and Iota map;
- all 24 round outputs against an independent native Keccak implementation;
- inactive storage rows, dead lanes, dead parity coordinates, and virtual
  nibble slots;
- all four extraction polynomials and the nibble validity polynomial;
- one invalid spread nibble;
- input-source, output-source, and source-MLE mutations;
- a row swap and a cross-permutation source swap;
- alternate coherent Iota constants;
- every payload section, truncation, trailing bytes, and noncanonical limbs;
- fixed-kernel evaluation against a naive wiring-table evaluator;
- both source folds against direct MLE evaluation;
- exact relation balance and exact retained table multiplicities;
- the complete theorem-negative roster;
- the A1/A2/B public-input-unlinkability test;
- the canonical `proveIdentity` and `verifyIdentity` path.

Every soundness-source commit MUST precede artifact generation. Regenerate the
generation input, shape manifest, circuit artifact, embedded circuit hash,
Android fixture, and fixed envelope. Run all proof tests in release mode with
12 Rayon workers and one test-harness thread.
