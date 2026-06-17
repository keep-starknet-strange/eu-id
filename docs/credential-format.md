# Simplified POC Credential Format (`C`)

> **Frozen interface contract.** Every cross-component binding relation — the
> SHA preimage field-exposure provider and the age / nationality credential
> bindings — keys off the field offsets below. **Do not change the layout once
> consumers exist.** The machine-readable source of truth is
> `crates/eu-id-prover/src/credential.rs`; this document is its prose mirror.

## Purpose & scope

`C` is the byte string an issuer hashes (SHA-256) and signs (ECDSA-P256 /
ES256) to attest a holder's attributes. For the MVP it is a deliberately
minimal, fixed byte-layout that **stands in for** an ISO/IEC 18013-5 mdoc — it
is *not* a real mdoc. There is no in-circuit CBOR/COSE parsing; full mdoc
support is the deferred credibility upgrade. Using
a simplified credential first lets the cross-component binding be proven before
taking on CBOR.

The format carries only what the two predicates consume — a date of birth and a
nationality — plus a magic header and a version byte. No issuer id, validity
window, or signature-suite bytes; those return with the full-mdoc work.

## Byte layout

Multi-byte integer fields are **big-endian**. Total length
**`CREDENTIAL_LEN` = 11 bytes**, which fits in a single 64-byte SHA-256 block,
so both fields live in block 0 and the field-exposure relation stays
single-block.

| offset | len | field        | encoding                                  |
|:------:|:---:|--------------|-------------------------------------------|
|   0    |  4  | magic        | ASCII `"EUID"` (`0x45 0x55 0x49 0x44`)    |
|   4    |  1  | version      | `0x01`                                    |
|   5    |  2  | birth year   | `u16` big-endian                          |
|   7    |  1  | birth month  | `u8` (`1..=12`)                           |
|   8    |  1  | birth day    | `u8` (`1..=31`)                           |
|   9    |  2  | nationality  | `u16` big-endian (ISO-3166-1 numeric)     |

Example — `2007-03-15`, Germany (`276` = `0x0114`):

```text
45 55 49 44 | 01 | 07 D7 | 03 | 0F | 01 14
^magic       ^ver ^year   ^mo  ^day ^nationality
```

`decode` checks only the structural invariants (length, magic, version).
Semantic field validity (a real calendar date, an assigned ISO code) is the
predicates' responsibility, not the format's.

## Field windows (what the bindings require)

The binding relations require exact byte windows of the SHA preimage:

| window               | offsets   | bytes                          |
|----------------------|-----------|--------------------------------|
| `DOB_WINDOW`         | `5..9`    | `year_hi, year_lo, month, day` |
| `NATIONALITY_WINDOW` | `9..11`   | `code_hi, code_lo`             |

### Byte ↔ value reconciliation

These are the equalities a binding relation proves between the exposed
credential bytes and the predicate's packed attribute (big-endian recomposition
— no digit arithmetic, by design):

```text
age:   year  = C[5] * 256 + C[6]
       month = C[7]
       day   = C[8]

nat:   code  = C[9] * 256 + C[10]
```

The age predicate stores its date of birth as a `(year, month, day)` triple
(bases 512 / 32); the binding proves that triple equals the values recomposed
from `DOB_WINDOW`. The nat predicate stores a single `u32` code; the binding
proves it equals the value recomposed from `NATIONALITY_WINDOW`.

## Signing (ES256)

`z = SHA-256(C)`; the issuer signs `z` with ECDSA-P256, producing `(r, s)`. The
verifier's public anchor is the issuer key `Q`. On the combined-proof path `z`
is *proven* equal to `SHA-256(C)` rather than supplied — only `Q` and the policy
are public.

## Native generator & oracle

`crates/eu-id-prover/src/generator.rs` is the out-of-circuit generator and the
ground-truth oracle:

- `IssuerKey` — an ECDSA-P256 signing key (demo seed `[7u8; 32]`, so `Q` and the
  fixtures are reproducible).
- `sign_credential(credential, issuer) -> SignedCredential` — emits `C`,
  `z = SHA-256(C)`, `(r, s)`, and `Q`.
- `PipelineWitness` — composes the per-module witnesses: the SHA-256 witness
  over `C`, the P256 proof draft over `(z, r, s, Q)`, and the age / nationality
  predicate inputs.
- `PipelineWitness::check_consistency()` — cross-checks against independent
  reference oracles (`sha2` and the `p256` crate, plus the in-repo native SHA /
  ECDSA references). It validates *self-consistency* (the crypto checks out and
  the predicate attributes match the signed bytes) — **not** the truth of the
  age / nationality statements, which the proof enforces.

## Reference policy & fixtures

The fixtures (`crates/eu-id-prover/src/fixtures.rs`) are judged against a fixed
policy: reference date **2026-06-17**, threshold **18**, accepted set
**{DE 276, FR 250, IT 380, ES 724}**.

| fixture               | crypto | binding | age ≥ 18 | nat ∈ set | verifies |
|-----------------------|:------:|:-------:|:--------:|:---------:|:--------:|
| `valid_over_18`       |   ✓    |    ✓    |    ✓     |     ✓     |    ✓     |
| `valid_exactly_18`    |   ✓    |    ✓    |    ✓     |     ✓     |    ✓     |
| `under_18`            |   ✓    |    ✓    |    ✗     |     ✓     |    ✗     |
| `wrong_nationality`   |   ✓    |    ✓    |    ✓     |     ✗     |    ✗     |
| `tampered_dob_bytes`  |   ✓    |    ✗    |   ✓\*    |     ✓     |    ✗     |
| `bad_signature`       |   ✗    |    ✓    |    ✓     |     ✓     |    ✗     |

`tampered_dob_bytes` (\*) is the credential↔predicate attack: a real under-18
credential is signed, but the age module is fed an over-18 date of birth. The
signature and the age sub-statement both pass — only the binding is broken,
which the age↔credential relation must catch. Each fixture isolates exactly one
property, so a later regression localises to the relation that broke.
