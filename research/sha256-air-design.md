# SHA-256 M31 AIR — Validated Design

> **Status:** validated & corrected design, ready to implement.
> **Validates:** `docs/sha256_air_design.md` (the bit-index-partitioned lookup-table sketch).
> **Supersedes:** `docs/sha256_air_design.md` for implementation purposes — implement *this*
> document, not the sketch and not the `../sha256-air` reference crate.
> **Audience:** the SHA-256 compression / multi-block AIR build, and the integration
> stream that binds the digest columns.

---

## 0. Verdict (read this first)

The bit-index-partitioned lookup-table approach in `docs/sha256_air_design.md` is **sound in
principle and worth implementing**. The decomposition trick — partition the 32 input bits of
each `Σ`/`σ` function into two 16-bit halves so that most output bits depend on only one half,
then table-lookup each half — checks out against the SHA-256 specification (FIPS 180-4).

However, the sketch must **not** be implemented verbatim. Validation found:

1. **One correctness bug** — the `Σ0` mixed-output set `O2` is listed with 8 entries; it must
   have 10. Implemented as written, two output bits of `Σ0` are never computed.
2. **One under-specified derivation** — the `{(a·11+b·20) mod 32}` index formula has a typo
   (`mod 2³²` should be `mod 32`) and, more importantly, **does not generalize**: the analogous
   construction for `Σ1` produces a *bad* partition (15 mixed bits, not 10). `Σ1` needs its own
   partition, which the sketch never gives.
3. **Five scope gaps** — the sketch covers a single compression half-round only. It omits the
   `Σ1` partition, the `σ0`/`σ1` message-schedule partitions (including how to handle the
   `SHR` term), multi-block chaining, padding, and finalization. All are required.
4. **Loose cost accounting** — the cell-cost figures are order-of-magnitude correct (~10⁴
   cells/block) but contain at least one arithmetic error and an unproven assumption.

The `../sha256-air` reference crate (a *different*, byte-level design) is **unsound** — its
constraint layer omits range checks and IV binding. Do not copy it. See §11.

This document supplies the corrected `Σ0`/`Σ1` partitions, the missing `σ0`/`σ1` partitions,
the table inventory and sizing, the M31 representation, and the multi-block / padding /
finalization design. Everything numeric here is reproduced by the script in Appendix A.

---

## 1. Bit-numbering convention (must be stated — classic bug source)

All bit indices in this document use **LSB-0 numbering**: bit `i` of a 32-bit word `w` has
value `2ⁱ`, so bit 0 is the least-significant bit. This matches Rust's `u32`:

- `ROTRⁿ(w)` ≡ `w.rotate_right(n)` — output bit `i` = input bit `(i + n) mod 32`.
- `SHRⁿ(w)` ≡ `w >> n` — output bit `i` = input bit `i + n` if `i + n < 32`, else `0`.

> **Note on the sketch.** `docs/sha256_air_design.md` numbers bits in the opposite (MSB-0)
> direction — its `Σ0` output set `O0 = {0,1,9,…}` only reproduces under MSB-0. The partition
> *as a set of input-bit indices* is convention-independent and yields the same 11/11/10 split
> either way; only the output-bit **labels** differ. The implementation and the witness
> generator must pick **one** convention and use it everywhere. We pick LSB-0 because the
> native (out-of-circuit) reference will use `u32::rotate_right` / `>>` directly. Every table
> below is LSB-0.

---

## 2. SHA-256 recap (the specification being validated against)

SHA-256 operates on 32-bit words. Source of truth: **FIPS 180-4 §4.1.2, §5.3.3, §6.2**.

Per-word functions:

| Function | Definition |
|---|---|
| `Σ0(a)` | `ROTR2(a) ⊕ ROTR13(a) ⊕ ROTR22(a)` |
| `Σ1(e)` | `ROTR6(e) ⊕ ROTR11(e) ⊕ ROTR25(e)` |
| `σ0(x)` | `ROTR7(x) ⊕ ROTR18(x) ⊕ SHR3(x)` |
| `σ1(x)` | `ROTR17(x) ⊕ ROTR19(x) ⊕ SHR10(x)` |
| `Ch(e,f,g)` | `(e ∧ f) ⊕ (¬e ∧ g)` — bitwise |
| `Maj(a,b,c)` | `(a ∧ b) ⊕ (a ∧ c) ⊕ (b ∧ c)` — bitwise |

Message schedule: `W[0..15]` are the block words; for `t = 16..63`,
`W[t] = σ1(W[t−2]) + W[t−7] + σ0(W[t−15]) + W[t−16]` (mod 2³²).

Round, for `t = 0..63`, working state `(a..h)`:
`T1 = h + Σ1(e) + Ch(e,f,g) + K[t] + W[t]`; `T2 = Σ0(a) + Maj(a,b,c)`; then
`(a,b,c,d,e,f,g,h) ← (T1+T2, a, b, c, d+T1, e, f, g)` (all `+` mod 2³²).

`K[0..63]` are the 64 round constants (`K[0] = 0x428a2f98 … K[63] = 0xc67178f2`).
The initial hash value `H = (H₀..H₇) = (0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19)`.

Finalization, after 64 rounds of block `t`: `Hⱼ ← Hⱼ + (working varⱼ)` mod 2³², for `j = 0..7`.
The 256-bit digest is `H₀‖…‖H₇` after the last block, each word emitted big-endian.

---

## 3. M31 representation — validated

The base field is M31 (`p = 2³¹ − 1`). A 32-bit word `w` is stored as **two 16-bit limbs**:

```
w.lo = w & 0xFFFF        w.hi = w >> 16        w = w.lo + 2¹⁶ · w.hi
```

Each limb is an M31 element in `[0, 2¹⁶)`.

**Headroom check (no aliasing in M31).** The widest addition in SHA-256 is `a_new = T1 + T2`,
a sum of **7** 32-bit words (`h, Σ1, Ch, K, W, Σ0, Maj`). Summing 7 low limbs:
`7 · (2¹⁶ − 1) = 458 745 < 2¹⁹`. The carry into the high limb is `≤ 6`; the high-limb sum is
`7 · (2¹⁶ − 1) + 6 < 2¹⁹`. Both are `≪ p = 2³¹ − 1` — roughly **12 bits of headroom**. The
message-schedule add (4 words) and finalization add (2 words) are smaller. **The 16-bit split
is sound; no constraint equation can alias to zero in M31.** (Unlike the ECDSA component, the
SHA-256 component has no headroom-audit blocker.)

Why 16+16 and not 4×8 (bytes): the `Σ`/`σ` lookups are keyed on 16-bit half-words (§5). A
32-bit word cannot be a single limb (`2³² > p`). 16+16 is the natural minimum that aligns with
the lookup-key width. **Decision: 2 × 16-bit limbs, little-endian limb order, per word.**

---

## 4. The decomposition principle

A 32-bit lookup `word → F(word)` would need a 2³² -row table — infeasible. The trick:

`Σ` and `σ` are **GF(2)-linear** maps (XORs of rotates/shifts). Each *output* bit depends on a
small set of *input* bits (3 for `Σ`; 2 or 3 for `σ`). Choose a 16-element subset `S` of the 32
input-bit positions. Classify each output bit `i` by its dependency set `D(i)`:

- `D(i) ⊆ S` → call it **O0** (computable from the `S` half alone),
- `D(i) ⊆ S'` (the complementary 16 bits) → **O1**,
- otherwise → **O2** (mixed — needs bits from both halves).

Then: one table maps the 16 `S`-bits → `{O0 bits} ∪ {O2 partial}`; a second maps the 16
`S'`-bits → `{O1 bits} ∪ {O2 partial}`; the two `O2` partials are XOR-combined (a third,
generic lookup). Because `O0 ⊎ O1 ⊎ O2` partitions all 32 output bits and the three groups are
bit-disjoint, the result word reassembles by **field addition** of the spread parts (disjoint
bit sets ⇒ `+` equals `⊕`). The whole function costs **3 lookups** plus the split.

`Maj`/`Ch` are **bitwise** (output bit `i` depends only on input bit `i` of each operand), so
they work with *any* partition and reuse the same split as `Σ`.

The design quality is entirely in **choosing `S` to minimise `|O2|`**. The sketch's
`{(a·11+b·20) mod 32}` construction is one way to find such an `S`; §6 shows it is correct for
`Σ0` but **not** a general recipe.

---

## 5. Validation findings — summary

| # | Item | Sketch says | Validated finding |
|---|---|---|---|
| F1 | `Σ0` partition `L0/L1/L2 + H0/H1/H2` | 6 groups, `S = L0‖H0‖H1` | **Correct.** Partitions `{0..31}`; `S` gives an 11/11/10 split. |
| F2 | `Σ0` output set `O2` | `{2,3,8,13,14,18,19,24}` (8 entries) | **BUG.** Must be 10 entries — `{29,30}` missing (sketch's own prose says "10"). |
| F3 | `{(a·11+b·20) mod 2³²}` formula | as written | **Typo:** `mod 2³²` → `mod 32`. Result set is correct for `Σ0`. |
| F4 | "9 free + 2 extra → 11" derivation | as written | **Correct** for `Σ0` (verified by exhaustive enumeration). |
| F5 | `Σ1` partition | not given (cost assumed = `Σ0`) | **Gap.** The analogous `{(a·5+b·19) mod 32}` set gives `|O2| = 15`, not 10. `Σ1` needs its own partition — supplied in §7. |
| F6 | `Maj` / `Ch` decomposition | "≤21-bit lookup tables, 6 parts" | **Correct** (bitwise ⇒ partition-agnostic). Table *sizing* under-specified — settled in §9. |
| F7 | `σ0` / `σ1` schedule partition | "in a very similar fashion", "split to 4 parts" | **Gap.** `SHR` is not a rotation; the rotation-factoring trick does not apply. Partitions supplied in §8. |
| F8 | Cell cost ≈ 9696 / block | as written | Order-of-magnitude OK. One arithmetic error (`6·2T = 18T`); `L = 2T` is an unjustified heuristic; `Σ1 ≡ Σ0` cost assumed without deriving `Σ1`. See §10b. |
| F9 | Lookup-table sizes / packed-vs-unpacked | "≤21 bit", "stored unpacked" | Under-specified. Unpacked ⇒ table explosion. Settled in §9: **packed**, width-shared. |
| F10 | Multi-block / padding / finalization / IV | absent | **Gap.** Required. Specified in §10. |

The output-bit math is verified exhaustively (all 32 bits, every function) by Appendix A.

---

## 6. `Σ0` — partition validated, `O2` corrected

`Σ0(a) = ROTR2(a) ⊕ ROTR13(a) ⊕ ROTR22(a)`. Output bit `i` depends on input bits
`D(i) = {(i+2) mod 32, (i+13) mod 32, (i+22) mod 32}`.

### 6.1 Why the `{(a·11+b·20) mod 32}` construction works

Factor the common rotation: `ROTR13 = ROTR2∘ROTR11`, `ROTR22 = ROTR2∘ROTR20`, so
`Σ0 = ROTR2 ∘ g` with `g = id ⊕ ROTR11 ⊕ ROTR20`. For `g`, output bit `j` depends on input
bits `{j, j+11, j+20}` (mod 32). Take `S = {(11a + 20b) mod 32 : 0 ≤ a,b < 4}` — **16 distinct
indices** (verified). For `j = 11a + 20b` with `a,b ∈ {0,1,2}`: `j+11 = 11(a+1)+20b ∈ S` and
`j+20 = 11a+20(b+1) ∈ S` (and `j ∈ S` trivially), so **9** output bits of `g` are guaranteed
internal to `S`. Exhaustive enumeration then finds **2 more** that also land inside `S`, for 11
total; `Σ0 = ROTR2∘g` only relabels output bits, so `Σ0` likewise splits 11 / 11 / 10.
**`mod 32`, not `mod 2³²`** — bit indices of a 32-bit word live in `0..31`.

This `S` equals the sketch's `L0 ∪ H0 ∪ H1`. The construction is **valid for `Σ0`** — but it
is *not* a general recipe (see §7).

### 6.2 The validated partition (LSB-0)

`S = {0,1,7,8,9,10,11, 18,19,20,21,22, 28,29,30,31}` — the six groups (each ≤ 7 bits, each
within one 16-bit half, three composing `S`, three composing `S'`):

| Group | Bits | Size | In |
|---|---|---|---|
| `L0` | `{0,1,7,8,9,10,11}` | 7 | `S` |
| `H0` | `{18,19,20,21,22}` | 5 | `S` |
| `H1` | `{28,29,30,31}` | 4 | `S` |
| `L1` | `{2,3,4,5,6}` | 5 | `S'` |
| `L2` | `{12,13,14,15}` | 4 | `S'` |
| `H2` | `{16,17,23,24,25,26,27}` | 7 | `S'` |

### 6.3 Output-bit sets — **CORRECTED**

Exhaustively classifying all 32 output bits (Appendix A):

| Set | LSB-0 (this design) | Count |
|---|---|---|
| `O0` (from `S`) | `{6,7,8,9,17,18,19,20,28,29,30}` | 11 |
| `O1` (from `S'`) | `{1,2,3,4,12,13,14,22,23,24,25}` | 11 |
| `O2` (mixed) | `{0,5,10,11,15,16,21,26,27,31}` | 10 |

> **F2 — the bug.** In `docs/sha256_air_design.md` (MSB-0 numbering), the correct sets are
> `O0 = {0,1,9,10,11,12,20,21,22,23,31}`, `O1 = {4,5,6,7,15,16,17,25,26,27,28}`,
> `O2 = {2,3,8,13,14,18,19,24,`**`29,30`**`}`. The sketch lists `O2` as
> `{2,3,8,13,14,18,19,24}` — **8 entries; bits 29 and 30 are missing.** The sketch's own prose
> says "The other 10 output bits", and `11 + 11 + 8 = 30 ≠ 32`, so the list — not the concept —
> is wrong. **If implemented verbatim, the `S`-table never emits `Σ0` output bits 29 and 30**
> (MSB-0); those two bits of every `Σ0` are silently zero ⇒ wrong digest ⇒ unsound. Use the
> 10-entry `O2` above.

---

## 7. `Σ1` — partition supplied (sketch gap F5)

`Σ1(e) = ROTR6(e) ⊕ ROTR11(e) ⊕ ROTR25(e)`; `D(i) = {(i+6), (i+11), (i+25)} mod 32`.

**The sketch never gives a `Σ1` partition** — it computes one half-round and assumes the other
costs the same. Applying the §6.1 construction by analogy (factor `ROTR6`; offsets become
`{0,5,19}`; `S = {(5a+19b) mod 32}`) produces:

`S = {0,2,3,5,6,8,10,11,15,16,19,21,24,25,29,30}` → split **9 / 8 / 15** (`|O2| = 15`).

**That is a bad partition** — `|O2| = 15` means a 15-bit `O2` and a 2³⁰ -row XOR table. The
construction is *not* a general recipe; `Σ1` must be solved directly. A search over `S`
(minimise `|O2|`, exhaustively verified — Appendix A) yields a partition matching `Σ0`'s
quality:

`S = {2,3,6,7,11,12, 16,17,20,21,24,25,26, 29,30,31}`

| Group | Bits | Size | In |
|---|---|---|---|
| `Le0` | `{2,3,6,7,11,12}` | 6 | `S` |
| `He0` | `{16,17,20,21,24,25,26}` | 7 | `S` |
| `He1` | `{29,30,31}` | 3 | `S` |
| `Le1` | `{0,1,4,5,8,9,10}` | 7 | `S'` |
| `Le2` | `{13,14,15}` | 3 | `S'` |
| `He2` | `{18,19,22,23,27,28}` | 6 | `S'` |

| Set | Bits (LSB-0) | Count |
|---|---|---|
| `O0` | `{0,1,5,6,10,14,18,19,23,24,28}` | 11 |
| `O1` | `{2,3,7,8,12,16,17,21,22,26,30}` | 11 |
| `O2` | `{4,9,11,13,15,20,25,27,29,31}` | 10 |

So `Σ1` *does* reach 11/11/10 — **but only after the search the sketch skipped**. The sketch's
"`Σ1` ≡ `Σ0` cost" assumption is now justified, not assumed.

The 6 groups satisfy the round constraints: each ≤ 7 bits (the `Maj`/`Ch` table cap), each
inside one 16-bit half, three composing `S` and three composing `S'`.

---

## 8. `Maj` / `Ch` and the message schedule `σ0` / `σ1`

### 8.1 `Maj` and `Ch` — validated

Both are **bitwise**: output bit `i` depends only on bit `i` of each operand. So a part-wise
table `(a_grp, b_grp, c_grp) → Maj_grp` (resp. `Ch`) works for **any** grouping — in
particular the §6/§7 round partitions, so `a` is split **once** and reused by both `Σ0` and
`Maj` (similarly `e` for `Σ1` and `Ch`). This is the sketch's "P(a,b,c)" treatment and it is
correct. Table sizing is settled in §9.

`Ch(e,f,g) = (e∧f) ⊕ (¬e∧g)` is a bit-multiplexer (`e ? f : g`). `Maj` is bitwise majority.
Both are precomputed exactly into their tables — no constraint subtlety.

> Optimisation (sketch silent): in a round, `b = old a`, `c = old b`. If a working
> variable's group split is **carried forward** in the trace, each value is split once, not
> three times. This cuts the per-round split cost by ⅔; fold it into the trace layout.

### 8.2 `σ0` / `σ1` — partitions supplied (sketch gap F7)

The sketch says only *"in a very similar fashion … split to 4 parts"*. It is **not** similar:
`σ0`/`σ1` contain a `SHR` term, which is **not a rotation**, so the §6.1 rotation-factoring
trick does not apply, and `SHR` makes some output bits depend on only **2** input bits (the
shifted-in zeros). The partitions are found by direct search + exhaustive verification.

`σ0`/`σ1` take a *single* input word and have no `Maj`/`Ch` to co-serve, so there is **no
≤7-bit group cap** — each function needs only a 16/16 split (4 "parts": `S∩lo`, `S∩hi`,
`S'∩lo`, `S'∩hi`, hence the sketch's "4 parts").

**`σ0(x) = ROTR7 ⊕ ROTR18 ⊕ SHR3`** — `S = {3,5,7,9,11,13,14, 16,18,20,22,24,26,28,30,31}`:

| Set | Bits (LSB-0) | Count |
|---|---|---|
| `O0` | `{0,2,4,6,13,17,19,21,23,28,30}` | 11 |
| `O1` | `{1,3,5,14,16,18,20,22,26,29,31}` | 11 |
| `O2` | `{7,8,9,10,11,12,15,24,25,27}` | 10 |

Parts: `S∩lo = {3,5,7,9,11,13,14}`, `S∩hi = {16,18,20,22,24,26,28,30,31}`,
`S'∩lo = {0,1,2,4,6,8,10,12,15}`, `S'∩hi = {17,19,21,23,25,27,29}`.

**`σ1(x) = ROTR17 ⊕ ROTR19 ⊕ SHR10`** — `S = {1,2,3,4,6,8,13,15, 17,20,22,24,26,27,29,31}`:

| Set | Bits (LSB-0) | Count |
|---|---|---|
| `O0` | `{3,5,7,10,12,14,16,17,19,21,28,30}` | 12 |
| `O1` | `{2,4,6,11,13,20,22,24,25,27,29,31}` | 12 |
| `O2` | `{0,1,8,9,15,18,23,26}` | 8 |

Parts: `S∩lo = {1,2,3,4,6,8,13,15}`, `S∩hi = {17,20,22,24,26,27,29,31}`,
`S'∩lo = {0,5,7,9,10,11,12,14}`, `S'∩hi = {16,18,19,21,23,25,28,30}`.
(`σ1` does better — `|O2| = 8` — because `SHR10` zeroes the dependency of 10 output bits.)

**`SHR` correctness in the table.** A `σ` decode table is preprocessed from the *true* `σ`
function, so `SHR` (zero-fill) is baked in correctly — there is **no** separate "force the
shifted-in bits to zero" constraint to forget. (The `../sha256-air` reference, §11, gets `SHR`
right in witness generation but its byte-decomposition design needs that extra constraint;
the lookup-table design here does not.)

**Schedule reuse caveat.** Each schedule word `W[j]` is the `σ0`-argument for one expansion
(`W[j+15]`) and the `σ1`-argument for another (`W[j+2]`). The two functions use **different**
partitions, so `W[j]` is split **twice** — once per partition. Budget for it.

---

## 9. Lookup-table inventory & sizing (sketch gaps F6, F9)

The sketch says "≤21-bit lookup tables" and "stored unpacked" without enumerating tables or
resolving the cost of "unpacked". Both are settled here.

### 9.1 Packed vs. unpacked — **decision: packed**

A "part" is the bits of a word at a group's positions. *Unpacked* = the word masked to those
positions (scattered bits, the sketch's choice). *Packed* = those bits compressed to
contiguous low positions.

- **Unpacked:** the `Maj`/`Ch` table column values are position-specific, so every
  `(function, group-position)` needs its **own** table — the a-side and e-side have 12 group
  positions ⇒ up to 12 distinct `Maj`/`Ch` tables, four of them 2²¹ rows. **Table explosion.**
- **Packed:** `Maj`/`Ch` are bitwise, so a packed table depends only on the group **width** —
  **one** table per width, shared across all positions and across `Maj` and `Ch`.

**Decision: pack the parts.** Packing costs one extra lookup layer — a "split-and-pack" table
per 16-bit half (maps the half to its packed groups). The net is far less preprocessed data.
This also makes every part the *output of a lookup*, which range-checks it for free (see §11,
lesson L1).

### 9.2 Group-width knob `W`

`Maj`/`Ch` part tables are 3-input; a width-`w` table has `2^(3w)` rows. `W` = max group width.

| `W` | `Maj`/`Ch` table rows | Groups / word | `Maj`+`Ch` lookups / round |
|---|---|---|---|
| 7 | 2²¹ (≈ 2.1 M) | 6 | 12 |
| **6** | **2¹⁸ (≈ 262 k)** | 6–8 | 12–16 |
| 5 | 2¹⁵ (≈ 33 k) | 8 | 16 |

`W` only affects the `Maj`/`Ch` tables and lookup count — the `Σ`/`σ` decode tables stay
2¹⁶ regardless (they are keyed by *all* groups of a half: `∏ 2^|gₖ| = 2¹⁶`, just more key
columns). **Recommended starting point: `W = 6`** — an 8× memory saving over the sketch's
implied `W = 7` for at most a modest lookup increase. Pad smaller groups into the single 2¹⁸
table (a 4-bit group is a 6-bit value with two bits forced 0). **Final `W` is pinned by the
laptop/mobile benchmark** — do not hard-code a number ahead of measured data.

### 9.3 Table inventory

| Table | Purpose | Rows | Count |
|---|---|---|---|
| `Maj`/`Ch` width-`W` | `(x,y,z) → (Maj,Ch)` of one packed group | `2^(3W)` (2¹⁸ at `W=6`) | 1 |
| `Σ0` decode `S`, `S'` | half → `O0`/`O1` spread + `O2` partial | 2¹⁶ | 2 |
| `Σ1` decode `S`, `S'` | as above | 2¹⁶ | 2 |
| `σ0` decode `S`, `S'` | as above | 2¹⁶ | 2 |
| `σ1` decode `S`, `S'` | as above | 2¹⁶ | 2 |
| split-and-pack | 16-bit half → packed groups + spread `S`/`S'` parts | 2¹⁶ | 8 (4 partitions × lo/hi half) |
| generic `XOR` | combine `O2` partials; reassembly | 2¹⁶ (8-bit chunks) | 1 |
| carry range-check | small-range check for addition carries | ≤ 2⁴ | 1 (or reuse shared range infra) |

≈ **19 preprocessed tables**, all 2¹⁶ except the `Maj`/`Ch` table and the small carry
range-check. At `W = 6`, total preprocessed columns ≈ low **tens of MB**; the `Maj`/`Ch`
table dominates and `W` tunes
it. **This is a mobile-memory input** — the mobile-backend feasibility research should budget
preprocessed-table RAM alongside the witness, since it is resident during proving.

> **Combine `O2` partials with the *generic* `XOR` table, not a per-function 2^(2·|O2|) table.**
> A naïve reading needs a 2²⁰ table for a 10-bit `O2`. Instead, chunk the two `O2` partials
> into ≤8-bit pieces and XOR chunk-wise through one shared 2¹⁶ `xor_8` table. This removes the
> three would-be 2²⁰ tables (`Σ0`/`Σ1`/`σ0`) entirely.

### 9.4 Use the shared foundation; do not fork range checks

The ECDSA stream owns the shared range-check / LogUp helpers (`Range*` tables,
`finalize_logup_in_pairs` pairing, the boolean helper). The SHA-256 component:

- **uses** the shared LogUp plumbing and, where a size matches, a shared range table for
  addition carries;
- **owns** the SHA-256-specific decode tables (`Maj`/`Ch`, `Σ`/`σ`) — these are not shared.

Settle the carry-range table choice with the ECDSA-stream owner before writing constraint
code (this is interface-contract item 4).

---

## 10. Round, addition, multi-block, padding, finalization

### 10.1 Round constraints (per round, 64 rounds/block)

Working state `a..h` held as `(lo,hi)` limb pairs. Per round:

1. Split `a` (a-side partition, §6) and `e` (e-side partition, §7) into packed groups via the
   split-and-pack tables; `b,c` and `f,g` reuse carried-forward splits (§8.1).
2. `Maj(a,b,c)`: one lookup per a-side group → `Maj` spread parts. `Ch(e,f,g)`: one per
   e-side group. Reassemble each by field addition of disjoint spread parts.
3. `Σ0(a)`: `S`-table + `S'`-table + `O2`-combine (§4). `Σ1(e)`: likewise. Reassemble.
4. `K[t]` is a circuit constant (`(lo,hi)` literals) — **hard-wired**, never a free column.
5. `T1 = h + Σ1 + Ch + K[t] + W[t]`; `T2 = Σ0 + Maj`; `e_new = d + T1`; `a_new = T1 + T2` —
   each a mod-2³² add (§10.2).
6. State update is **column relabeling** (`h←g`, …, `b←a`) — free.

Every constraint is degree ≤ 2 (lookups are degree-1 relations; the split/reassembly are
linear; carries are lookup-range-checked, §10.2). Keep it that way — it keeps LogUp numerator
degree at 1, matching the shared-foundation requirement.

### 10.2 Addition mod 2³²

To add `k` words (`k ≤ 7`) as `(lo,hi)` limbs:

```
sum_lo = Σ inputⱼ.lo        →  sum_lo = res.lo + 2¹⁶ · carry_lo
sum_hi = Σ inputⱼ.hi + carry_lo   →  sum_hi = res.hi + 2¹⁶ · carry_hi   (carry_hi discarded ⇒ mod 2³²)
```

Constraints: the two linear equations above, plus **range checks**:
`res.lo, res.hi ∈ [0, 2¹⁶)` and `carry_lo, carry_hi ∈ [0, k)`. The carry range check is a
lookup (preferred over a `carry·(carry−1)·… = 0` polynomial — lower degree). The result limbs
are range-checked **explicitly** unless they are immediately consumed by a lookup that
already pins them to `[0,2¹⁶)` (e.g. a split-and-pack table input next round) — see §11 L1.
Headroom: §3 (no M31 aliasing).

### 10.3 Multi-block chaining (sketch gap F10)

The credential structures hashed (`IssuerSignedItem`, COSE `Sig_structure`) exceed one
512-bit block, so multi-block is **mandatory**, not optional.

- `H⁽⁰⁾ = IV` — the 8 constants of §2. **Constrain `H⁽⁰⁾` equal to the IV constants**
  (do not read it as free columns — see §11 L2).
- Block `t` runs the schedule + 64 rounds with initial working state `H⁽ᵗ⁾`.
- Finalization: `H⁽ᵗ⁺¹⁾ⱼ = H⁽ᵗ⁾ⱼ + (working varⱼ after round 63)` mod 2³², `j = 0..7`
  (8 mod-2³² adds, §10.2).
- The trace binds consecutive blocks: block `t+1`'s initial state **is** `H⁽ᵗ⁺¹⁾` (a copy
  constraint or shared columns). The digest is `H⁽ⁿ⁾` after the final block `n−1`.

### 10.4 Padding (sketch gap F10)

FIPS 180-4 §5.1.1: for an `L`-bit message, append a `1` bit, then `k` zero bits
(`L+1+k ≡ 448 mod 512`), then `L` as a 64-bit big-endian integer. In bytes: append `0x80`,
then zero bytes, then the 8-byte big-endian **bit** length.

The preimage is a private witness, so padding **must be constrained** — otherwise a prover
hashes a differently-padded message. Constrain: the `0x80` marker is present at the correct
offset; all bytes between it and the length field are zero; the final 8 bytes encode the bit
length; total padded length is a multiple of 64 bytes. The message length feeding the length
field must itself be bound to the preimage length used by the mdoc/credential stream (so the
same bytes are hashed that are parsed) — interface-contract item 3.

### 10.5 Digest output layout (interface surface)

The 256-bit digest is exposed as **16 M31 limbs**: word order `H₀..H₇`, each word as
`(lo, hi)` (little-endian limb order, §3), every limb in `[0,2¹⁶)` and range-checked. The
SHA-256 byte string is `H₀..H₇` each serialised **big-endian**; byte values derive from the
limbs if a byte view is needed.

This component is used **twice** — `SHA-256(IssuerSignedItem) → elementDigest` and
`SHA-256(Sig_structure) → z`. Both digest outputs must be cleanly exposable as the 16-limb
block above so the integration stream can LogUp-bind them (`elementDigest` ↔ the
`valueDigests` membership check; `Sig_structure` digest ↔ the ECDSA `z` input).

> **Freeze with teammates before building (interface contract):** (1) this 16-limb digest
> layout — confirmed with the mdoc and integration owners; (2) the LogUp relation tag names
> for digest↔`valueDigests` and digest↔`z`; (3) the multi-block preimage-feeding convention,
> against the mdoc structure analysis that defines the byte layouts. Mismatched tags or limb
> layout = silent LogUp imbalance.

---

## 10b. Cost — corrected (sketch finding F8)

The sketch's "≈ 9696 cells/block" reproduces *only* under the unjustified assumption `L = 2T`
(a lookup costs twice a plain trace cell) and contains one hard error: step 1 is written
`6·2T = 18T`, but `6·2 = 12`. With the rest of the sketch's arithmetic that would change the
per-half-round figure; the sketch's totals are therefore not load-bearing.

A structural re-count (robust regardless of the `T`/`L` weighting):

| Phase | Lookups (each, approx.) | × | Subtotal |
|---|---|---|---|
| Round, a-side | split 2 + `Maj` `G` + `Σ0` 3 | | `5 + G` |
| Round, e-side | split 2 + `Ch` `G` + `Σ1` 3 | | `5 + G` |
| Round, adds | carry range-checks | | ≈ 5 |
| **Per round** | | × 64 | `64·(15 + 2G)` |
| Schedule entry | `σ0` 5 + `σ1` 5 + add ≈ 3 | × 48 | `48·13` |
| Finalization | 8 adds, carry checks | / block | ≈ 16 |

At `G = 6`: ≈ **2 380 lookups/block**; at `G = 8`: ≈ **2 640**. With comparable plain-cell
counts the total is order **10⁴ trace cells/block** — the *same magnitude* as the sketch's
9696, so the headline figure is plausible. But:

- `L = 2T` is a heuristic. A LogUp lookup adds extension-field interaction columns; with
  pair-batching the amortised cost is ≈ 1 interaction column per lookup, and interaction
  columns are ≈ 4× a base column. Real per-lookup cost is somewhere in `2T–4T`.
- The `Σ1 ≡ Σ0` cost the sketch assumed is **only** valid given §7's `Σ1` partition.

**The only trustworthy cost number is the measured benchmark.** This document fixes the
*structure*; the laptop benchmark (the post-week-2 go/no-go) produces the real proof-gen
time, proof size, and memory. If the primitives don't fit, that is a scope signal.

---

## 11. Reference audit — `../sha256-air`

The roadmap flagged `../sha256-air` as "possibly wrong". It is a **different design** —
byte-level (8-bit limbs, `xor_8_8`/`ch_8_8_8`/`maj_8_8_8` tables, rotation via
byte-decomposition, `add_mod_u32` carry chains) — and the eu-id component does **not** use it.
A full static audit of every source file (the crate compiles; prior build artifacts exist)
found:

**Confirmed soundness bugs — do not copy the constraint layer:**

1. **`add_mod_u32` has no range check** (`src/air/add_mod_u32.rs:29-95`). It constrains only
   the carry linear equation and `carry·(1−carry)=0` — **nothing forces output bytes
   `cᵢ ∈ [0,255]`**. A prover picks `cᵢ` as any field element and a matching carry. Modular
   addition — the core of SHA-256 — is *not* enforced. The crate's own
   `research/add_mod_u32.md:61-68` specifies the missing `rc_8` byte check; the code omitted
   it.
2. **Initial state never bound to the IV** (`src/air/compression.rs:38-43`). `initial_state`
   is read as free columns; `H` is never imported into the AIR. A prover may start
   compression from any state. (`K[t]` *is* correctly hard-wired — so the omission is
   inconsistent, not systematic.)
3. **Compression byte columns not range-checked** — most data-path bytes reach only the
   (broken) adder relation, never an 8-bit table.

**Why the test suite passes anyway:** every test feeds an *honest* trace, and honest traces
satisfy the (too-weak) constraints. Tests cover single-block only (≤ 55 bytes), check the
digest against the `sha2` crate, and check a tampered `claimed_sum` — but never feed a
*malformed trace* through constraint evaluation. The tests validate the witness *generator*,
not the *constraints*.

**Also:** single-block only (`lib.rs:65-69`); padding computed but **not constrained**;
finalization present but unsound (rests on bugs 1–2); one `add_mod_u32` constraint is degree 3
under a degree-2 bound (may mis-prove).

**Correct and reusable as learning material:** the constants (`K`, `IV` — spot-checked
against FIPS 180-4), the preprocessed `Maj`/`Ch`/`xor` table *contents*, the witness/trace
generator (verified against `sha2`), and the round/schedule *structure* (`T1`, `T2`, state
rotation, `W[t]` recurrence — all spec-correct).

**Verdict:** the reference's trace generation and component layout are instructive; its
**constraint layer is unsound and must not be trusted or copied**. Treat it (and
`../cosine-similarity-air`) as learning artifacts only — exactly as the roadmap directs.

### Lessons carried into this design

| # | Lesson (from a `../sha256-air` bug) | Applied here |
|---|---|---|
| L1 | Unconstrained limbs break soundness | **Every** M31 limb is range-checked — implicitly (it is a lookup input/output: the packed-parts and decode-table design makes nearly all values lookup-bound) or explicitly (output limbs not consumed by a lookup — §10.2, §10.5). |
| L2 | Initial state not bound to IV | `H⁽⁰⁾` is **constrained equal to the IV constants**; block chaining is a copy constraint (§10.3). |
| L3 | Padding computed but not constrained | Padding is **constrained** — `0x80` marker, zero fill, length field, block-multiple length (§10.4). |
| L4 | Tests only exercise honest traces | The build-phase test plan **must** include negative tests that feed malformed traces through constraint evaluation, plus **multi-block** vectors — not only honest single-block hashes vs. `sha2`. |
| L5 | Degree-3 constraint under degree-2 bound | Keep all constraints degree ≤ 2; range-check carries by **lookup**, not by polynomial identities (§10.1–10.2). |

---

## 12. Open decisions to freeze before / during the build

1. **Group-width `W`** — recommended `6`; pin against the laptop & mobile benchmarks (§9.2).
2. **Digest limb layout** — 16 limbs, `(lo,hi)` per word `H₀..H₇` (§10.5); confirm with the
   mdoc-membership and integration owners.
3. **LogUp relation tags** — for digest↔`valueDigests` and digest↔ECDSA-`z`; agree names with
   the other two stream owners up front.
4. **Carry range-check table** — reuse the ECDSA stream's shared range infrastructure where a
   size matches; settle before writing constraint code (§9.4).
5. **Preimage-feeding convention** — depends on the mdoc / COSE structure analysis (which
   exact `IssuerSignedItem` and `Sig_structure` bytes, with their padding). Align once that
   research lands.

---

## Appendix A — verification script

The `Σ1`, `σ0`, `σ1` partitions in §7–§8 were *found* by a min-`|O2|` search over the 16/16
input-bit splits (random restart + 1-swap hill-climbing); `Σ0`'s is the documented
`{(11a+20b) mod 32}` set. That search is a **discovery tool, not the design** — many distinct
`S` reach the same `|O2|`, so its raw output is RNG-dependent and not canonical. The design is
the four *explicit* partitions below; this script **verifies** them deterministically (no RNG)
by classifying all 32 output bits of each function and asserting against the §6–§8 tables.

```python
FULL = (1 << 32) - 1

def big(r1, r2, r3):              # Σ: XOR of three ROTR, LSB-0 (== u32::rotate_right)
    return [(1 << ((i+r1) % 32)) | (1 << ((i+r2) % 32)) | (1 << ((i+r3) % 32)) for i in range(32)]

def small(r1, r2, s):             # σ: ROTR r1 ^ ROTR r2 ^ SHR s
    d = []
    for i in range(32):
        m = (1 << ((i+r1) % 32)) | (1 << ((i+r2) % 32))
        if i + s < 32:            # SHR drops bits that would shift past bit 31
            m |= 1 << (i + s)
        d.append(m)
    return d

def classify(dep, S):             # O0 = D(i)⊆S, O1 = D(i)⊆S', O2 = mixed
    Sc = FULL ^ S
    return ([i for i in range(32) if dep[i] & S  == dep[i]],
            [i for i in range(32) if dep[i] & Sc == dep[i]],
            [i for i in range(32) if dep[i] & S != dep[i] and dep[i] & Sc != dep[i]])

def mask(it):
    m = 0
    for i in it: m |= 1 << i
    return m

# The design: function, S (the 16-bit "good" set), and expected O0 / O1 / O2 from §6–§8.
DESIGN = {
  "Σ0": (big(2, 13, 22),    {0,1,7,8,9,10,11, 18,19,20,21,22, 28,29,30,31},
         [6,7,8,9,17,18,19,20,28,29,30], [1,2,3,4,12,13,14,22,23,24,25], [0,5,10,11,15,16,21,26,27,31]),
  "Σ1": (big(6, 11, 25),    {2,3,6,7,11,12, 16,17,20,21,24,25,26, 29,30,31},
         [0,1,5,6,10,14,18,19,23,24,28], [2,3,7,8,12,16,17,21,22,26,30], [4,9,11,13,15,20,25,27,29,31]),
  "σ0": (small(7, 18, 3),   {3,5,7,9,11,13,14, 16,18,20,22,24,26,28,30,31},
         [0,2,4,6,13,17,19,21,23,28,30], [1,3,5,14,16,18,20,22,26,29,31], [7,8,9,10,11,12,15,24,25,27]),
  "σ1": (small(17, 19, 10), {1,2,3,4,6,8,13,15, 17,20,22,24,26,27,29,31},
         [3,5,7,10,12,14,16,17,19,21,28,30], [2,4,6,11,13,20,22,24,25,27,29,31], [0,1,8,9,15,18,23,26]),
}
for name, (dep, S, e0, e1, e2) in DESIGN.items():
    O0, O1, O2 = classify(dep, mask(S))
    assert len(S) == 16, name
    assert (O0, O1, O2) == (sorted(e0), sorted(e1), sorted(e2)), name   # matches §6–§8
    assert len(set(e0) | set(e1) | set(e2)) == 32                       # O0 ⊎ O1 ⊎ O2 = all 32 bits
    print(f"{name}: |O0|={len(O0)}  |O1|={len(O1)}  |O2|={len(O2)}  verified")

# F3: the documented Σ0 set equals {(11a + 20b) mod 32}  — note mod 32, not mod 2**32.
assert mask({0,1,7,8,9,10,11,18,19,20,21,22,28,29,30,31}) == \
       mask({(11*a + 20*b) % 32 for a in range(4) for b in range(4)})
print("F3 (Σ0 partition == {(11a+20b) mod 32}): verified")

# F5: the analogous {(5a+19b) mod 32} construction is a *bad* Σ1 partition.
bad = classify(big(6, 11, 25), mask({(5*a + 19*b) % 32 for a in range(4) for b in range(4)}))
assert [len(x) for x in bad] == [9, 8, 15]
print("F5 ({(5a+19b) mod 32} for Σ1): split 9/8/15 -> bad, |O2|=15, confirmed")
```

Expected output — every line ends `verified` / `confirmed`:

```
Σ0: |O0|=11  |O1|=11  |O2|=10  verified
Σ1: |O0|=11  |O1|=11  |O2|=10  verified
σ0: |O0|=11  |O1|=11  |O2|=10  verified
σ1: |O0|=12  |O1|=12  |O2|=8  verified
F3 (Σ0 partition == {(11a+20b) mod 32}): verified
F5 ({(5a+19b) mod 32} for Σ1): split 9/8/15 -> bad, |O2|=15, confirmed
```

Each passing `assert` *is* the validation: the partition has 16 input bits, the three output
sets match §6–§8 exactly, and `O0 ⊎ O1 ⊎ O2` covers all 32 output bits. The `Σ0` `O2` has
**10** entries, not the 8 the sketch lists — finding F2.

---

## Appendix B — requirement coverage

| Validation requirement | Where |
|---|---|
| Verify the `L0/L1/L2 + H0/H1/H2` partition and the `Σ`/`Ch`/`Maj` lookup decomposition | §4, §6, §7, §8 |
| Confirm cell costs and the `{(a·11+b·20) mod 32}` derivation | §6.1 (derivation, typo F3), §10b (cost F8) |
| Independently audit `../sha256-air` for correctness | §11 |
| Settle lookup-table sizes and the M31 representation | §3 (M31), §9 (tables) |
| Multi-block hashing present in the validated design | §10.3, §10.4, §10.5 |
| Deliverable: `research/sha256-air-design.md` | this file |
