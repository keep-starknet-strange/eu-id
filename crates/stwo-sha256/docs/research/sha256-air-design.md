# SHA-256 AIR implementation invariants

This document describes the current `stwo-sha256` implementation.
It does not describe a future design.
The Rust source and its tests are the final authority.

## 1. Trace model

The AIR uses one natural row for each SHA-256 round.
One padded 512-bit block uses 64 rows.
Block `b`, round `t`, uses natural row `64 * b + t`.

The trace size is a power of two.
`trace::min_log_size` always leaves at least one disabled row after the real
rows.
The last-block gate uses this row to identify the final real row.

The `enabler` column is Boolean.
The contiguity constraints permit one enabled prefix only.
The first enabled row must be natural row zero.
Disabled arithmetic cells can contain random decoy values.
All public role flags are zero on disabled rows.

## 2. Bit, word, and byte conventions

All committed word bits use LSB-0 numbering.
Bit `i` of word `w` has value `2^i`.
The AIR uses these formulas:

- `ROTR^n(w)[i] = w[(i + n) mod 32]`.
- `SHR^n(w)[i] = w[i + n]` when `i + n < 32`.
- `SHR^n(w)[i] = 0` when `i + n >= 32`.

The AIR constrains every committed input bit to be Boolean.
It recomposes each 32-bit word from two 16-bit limbs:

```text
w = lo + 2^16 * hi
```

The trace stores the limbs in `(lo, hi)` order.
SHA-256 parses each 64-byte block as 16 big-endian words.
The final digest uses word order `H[0]` through `H[7]`.
Each digest word uses big-endian byte order:

```text
[hi.b1, hi.b0, lo.b1, lo.b0]
```

The AIR recomposes each digest limb from two bytes.
The `Range_8` relation constrains each digest byte to `[0, 256)`.

## 3. M31 arithmetic and headroom

The base field modulus is `p = 2^31 - 1`.
The centered limit is:

```text
(p - 1) / 2 = 2^30 - 1 = 1_073_741_823
```

Each modular addition uses these two integer identities:

```text
sum(addend.lo)            = result.lo + 2^16 * carry_lo
sum(addend.hi) + carry_lo = result.hi + 2^16 * carry_hi
```

The AIR discards `carry_hi`.
This gives addition modulo `2^32`.

For an addition with `k` addends, both carries must be in `[0, k)`.
The AIR uses one range relation for each active bound:

| Addition family | `k` | Relation | Maximum audited absolute expression |
|---|---:|---|---:|
| `T2`, `e_new`, `a_new`, finalization | 2 | `Range_2` | 262,142 |
| Message-schedule recurrence | 4 | `Range_4` | 524,286 |
| `T1` | 5 | `Range_5` | 655,358 |

The audit uses this bound for a canonical witness. It assumes that each
result limb is in `[0, 2^16)`.

```text
(k + 1) * (2^16 - 1) + carry_in + 2^16 * (k - 1)
```

Under this assumption, all active families are below the centered M31 limit.
The widest family is `T1`.
Its bound is more than 10 bits below the centered limit.
`headroom::current_headroom_audits` lists all active addition families.
Its tests fail if a family has no formula or exceeds the limit.
This audit checks the values that the canonical witness generator produces.
It does not prove that the AIR range-checks every result limb. In particular,
the AIR does not bit-recompose or range-check the `T1` and `T2` result limbs
directly.

## 4. SHA-256 function constraints

The active AIR computes the SHA-256 functions from Boolean word bits.
It does not use function lookup relations.

The AIR constrains:

- `Σ0(a) = ROTR2(a) XOR ROTR13(a) XOR ROTR22(a)`;
- `Σ1(e) = ROTR6(e) XOR ROTR11(e) XOR ROTR25(e)`;
- `σ0(x) = ROTR7(x) XOR ROTR18(x) XOR SHR3(x)`;
- `σ1(x) = ROTR17(x) XOR ROTR19(x) XOR SHR10(x)`;
- `Ch(e,f,g) = g XOR (e AND (f XOR g))`;
- `Maj(a,b,c)` as the bitwise majority of `a`, `b`, and `c`.

The AIR recomposes each function output into its two word limbs.
It also binds the repeated round-state bit columns to their source rows.

For `t` in `[16, 64)`, the AIR constrains:

```text
W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16] mod 2^32
```

For each round, it constrains:

```text
T1    = h + Σ1(e) + Ch(e,f,g) + K[t] + W[t] mod 2^32
T2    = Σ0(a) + Maj(a,b,c) mod 2^32
e_new = d + T1 mod 2^32
a_new = T1 + T2 mod 2^32
```

The round constants `K[t]` are preprocessed constants.
They are not witness values.

## 5. Initial state, block chain, and final digest

The first block input state is the eight SHA-256 IV constants.
The AIR binds these constants on the first real row.
It also binds the first-block flag to the preprocessed first-row selector.
This prevents a cyclic predecessor row from replacing the IV.

For each continuation block, the AIR constrains:

```text
current.h_in[j] = previous.h_out[j]
```

After round 63, the AIR constrains each finalization word:

```text
h_out[j] = h_in[j] + working[j] mod 2^32
```

The `is_last_block` constraint selects the final enabled block.
When digest exposure is active, that block yields one 32-byte digest tuple.
Intermediate block states do not yield digest tuples.

## 6. Padding constraints

The padding witness is active on each block's round-15 row.
The AIR constrains the role flags and marker selectors to be Boolean.
For a marker block, it constrains:

- one marker word;
- one marker byte in that word;
- marker value `0x80`;
- zero bytes after the marker in that word;
- zero words after the marker, except for the final length words.

For a length block, the AIR binds `W[14]` and `W[15]` to the four committed
bit-length limbs.
The trace structure makes the padded byte length a multiple of 64.

The standalone AIR does not require a marker role or a length role to occur.
An all-zero set of padding role flags makes the marker and length constraints
inactive. Therefore, the standalone component does not prove complete FIPS
180-4 padding by itself.

The complete padded-stream mode also binds the configured block count.
Its block counter starts at zero.
It is constant within a block.
It increments by one between blocks.
Its final value must equal `padded_len / 64 - 1`.

A composed protocol must bind the padded bytes to a parser that defines the
message, its length, and its padding. The full padded-stream relation provides
this binding surface. The TS13 composition uses this binding to make the
padding claim complete.

## 7. Live LogUp relations

The current SHA-256 component uses only these relation families:

| Relation | Tuple | Purpose |
|---|---|---|
| `Range_2` | `(value)` | Two-addend carries |
| `Range_4` | `(value)` | Four-addend carries |
| `Range_5` | `(value)` | Five-addend carries |
| `Range_8` | `(value)` | Final digest bytes |
| `Sha256Digest` | 32 digest bytes | Bind the final SHA-256 digest to another component |
| `Sha256Field` | `(field_id, byte_index, value)` | Bind every padded message byte to another component |

The full padded-stream provider yields 64 field tuples on each enabled
block's round-15 row.
It derives each value from the constrained LSB-0 word bits.
It emits bytes in block order and big-endian word order.
The byte index is:

```text
64 * block_counter + byte_in_block
```

The transcript binds the field ID, padded length, provider mode, relation
shape, and trace shape.
The prover and verifier draw all relation challenges in the same fixed order.

Every provider needs a matching consumer in a composed proof.
An unconsumed digest or field provider gives a nonzero global claimed sum.
Verification rejects that proof.
Shared range-table producers use the same relation challenges as all SHA
consumers.

## 8. Verification requirements

The fast tests check these invariants:

- native SHA-256 results for single-block and multi-block messages;
- all M31 headroom formulas and range bounds;
- honest linear constraints for single-block and multi-block traces;
- full padded-stream block count, byte order, byte indices, and totality;
- range multiplicity totals and out-of-range mutations;
- digest-byte recomposition and `Range_8` balance;
- fresh disabled-row decoys with public flags set to zero.

The negative linear tests change one trace property at a time.
They cover the schedule, carries, sigma outputs, IV anchor, block chain,
padding marker, enabled-row contiguity, padding-row flags, and stream length.

The release proof tests cover the complete STARK and LogUp path.
They cover padding boundaries, long messages, shared tables, claimed-sum
tampering, and unconsumed digest or field providers.
The slow proof tests are ignored by the default test command.
Run them explicitly in release mode.

The standalone `Sha256Proof.digest` and `Sha256Proof.n_blocks` fields are
witness metadata.
The standalone verifier does not bind these fields to the AIR.
A composed proof must use the digest relation or the full padded-stream
relation for the required external binding.

This implementation has not had an external security audit.
STWO does not provide zero knowledge.
