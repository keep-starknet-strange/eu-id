# SHA-256 M31 AIR design

## Status

This document describes the active implementation on `build/release-lto`.
The Rust source and tests are the authority for exact column positions.

The active AIR uses Boolean bit planes. It does not use the compatibility
decode, packed Maj/Ch, XOR, or split-pack tables.

## Row model

One SHA-256 block uses 67 trace rows: three state-seed rows followed by 64
compression-round rows. Round `t` has natural row index
`block * 67 + 3 + t`.

Stwo stores rows in bit-reversed circle-domain order. Cross-row masks read
earlier rounds, earlier schedule words, and the prior block output.

The trace size is a power of two. It is strictly larger than the real row
count. Disabled random decoy rows fill the remaining space.

## Word representation

The trace represents each 32-bit word as two 16-bit M31 limbs:

```text
word = lo + 2^16 * hi
```

Committed bit planes constrain each word. The least significant bit comes
first. Limb recomposition ties the bit planes to the arithmetic columns.

The M31 headroom audit covers each addition family. See
`crates/stwo-sha256/src/headroom.rs`.

## SHA equations

Rounds 16 through 63 use this schedule equation:

```text
W[t] = W[t-16] + σ0(W[t-15]) + W[t-7] + σ1(W[t-2]) mod 2^32
```

Each compression round uses these equations:

```text
T1 = h + Σ1(e) + Ch(e, f, g) + K[t] + W[t] mod 2^32
T2 = Σ0(a) + Maj(a, b, c) mod 2^32
e' = d + T1 mod 2^32
a' = T1 + T2 mod 2^32
```

The AIR computes `Σ0`, `Σ1`, `σ0`, `σ1`, `Maj`, and `Ch` from Boolean bit
planes. `crates/stwo-sha256/src/native.rs` supplies the native reference.

## Addition constraints

Each modulo-2³² addition has one equation for each limb:

```text
sum(addend.lo) = result.lo + 2^16 * carry_lo
sum(addend.hi) + carry_lo = result.hi + 2^16 * carry_hi
```

The active range relations are:

- `Range_2` for two-addend operations
- `Range_4` for the schedule operation
- `Range_5` for `T1`
- `Range_8` for digest bytes

The LogUp producer tables contain all valid values. Consumer and producer
terms must cancel.

## State chain

The preprocessed `is_first_row` selector anchors the first block. The first
three rows seed `h3/h7`, `h2/h6`, and `h1/h5`; round zero seeds `h0/h4` in
the rolling `a/e` bit lanes. The AIR requires the SHA-256 initial value on
every packed message start.

Each round reads the current `a/e` lanes and the prior three rolling rows to
recover all eight state words. Round 63 produces the compression result.

Each continuation block receives the prior block output. Every message start
resets to the IV, and the packed metadata columns enforce message/block
ordering. A contiguity constraint prevents disabled rows inside the real row
region.

Finalization adds the input hash state to the compression result. The final
real block supplies the digest bytes.

## FIPS padding

The AIR checks the FIPS 180-4 padding structure. It checks:

- the `0x80` marker
- each zero after the marker
- the final 64-bit message length
- marker and length block roles
- one-hot marker positions

Padding data occupies the round-15 row of each block. The AIR reads the 16
message words through cross-row masks.

## Preprocessed columns

The standalone component commits 14 preprocessed columns:

- four `Range_k` value columns
- one `is_first_row` selector
- nine round-cyclic columns

The round-cyclic columns contain the round constant limbs and selectors. The
prover and verifier identify each column by a stable name.

## Digest relation

The digest provider emits 32 big-endian final-block bytes. A consumer must
require the same tuple on the shared digest relation.

The standalone proof has no digest consumer. It keeps the provider off by
default. A provider without a consumer gives a nonzero LogUp total.

## Full-stream field relation

The optional packed-stream provider emits every padded-stream byte. Each tuple
contains `(BASE + message_id, byte_index, byte_value)`, where `byte_index`
starts at zero for each message and advances across its 64-byte blocks.
The AIR derives four bytes from the existing `W` bit planes on each input-word
round `t = 0..15`.

A consumer component must require each emitted byte on the same shared field
relation. The standalone proof leaves this provider off by default.

## Shared range tables

A composed proof can move fixed range providers into one shared module. Each
SHA consumer then keeps only its range-consumer terms.

Class-D masking doubles each shared producer domain. The lower half contains
the real multiplicities. The upper half contains fresh random multiplicities
at unreachable dummy keys.

An `is_dummy` gate gives each dummy row a zero numerator. Dummy values do not
change the LogUp total. Tests check the domain size, random upper half, and
claimed-sum tamper rejection.

## Security boundary

The AIR constrains SHA execution, block chaining, finalization, and padding.
Range relations constrain carries and digest bytes.

`Sha256Proof` contains no digest or block-count metadata. The standalone
verifier intentionally has no exact consumer. A composed product proof must
bind each digest and padded stream through the keyed shared relations.

Claim masks and dummy rows hide selected interaction values. They do not give
proof-wide zero knowledge. The current proof is transparent and does not
guarantee witness confidentiality or unlinkability.

## Verification

Run the standard tests:

```bash
cargo test -p stwo-sha256
```

Run the ignored proof tests in release mode:

```bash
cargo test --release -p stwo-sha256 \
  --test prove_verify_round_trip -- --ignored
```

Negative tests change limbs, carries, selectors, padding data, and relation
claims. Verification must reject each invalid case.
