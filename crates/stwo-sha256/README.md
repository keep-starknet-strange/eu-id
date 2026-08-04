# stwo-sha256

SHA-256 STARK AIR over the M31 field for the `eu-id` credential pipeline,
built on [Stwo](https://github.com/starkware-libs/stwo).

> **Status — research prototype.** This crate is not audited.
> It produces succinct proofs, but it does not yet produce zero-knowledge proofs.
> See the workspace [`README`](../../README.md) for the project context.

## What this crate proves

For a private message `m`, `prove_sha256` packs that one message through the
sole packed component and produces a STARK proof for a valid SHA-256 trace.
The AIR constrains each schedule word and each round state.
It also constrains the block states, FIPS padding, and multi-block chain.
Product integration binds each digest and complete padded byte stream through
the keyed cross-component relations.

## Quick start

```bash
# unit tests + integration tests, debug (~1 s)
cargo test -p stwo-sha256

# the real prove → verify round-trip on b"abc" (~8 s in release)
cargo test --release -p stwo-sha256 --test prove_verify_round_trip -- --ignored

# end-to-end demo on a default or custom message
cargo run --release --example prove_demo -p stwo-sha256
cargo run --release --example prove_demo -p stwo-sha256 -- "the quick brown fox"
```

The release round trip has the `#[ignore]` attribute because proof generation is slow.
Run it with `--ignored` or `make`.

## What the AIR enforces today

| Soundness obligation             | Status                                                                                                                                                                      |
| -------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Every round word is bit-constrained | Enforced — the bit-plane identities reconstruct round words; each terminal `h_out` limb is recomposed from two explicit `Range_8`-checked bytes.                                              |
| Every mod-2³² limb-add identity | Enforced — schedule recurrence, `T1`, `T2`/`e_new`/`a_new`, and the 8 finalization adds emit linear constraints **and** range-check their carries against `Range_{2,4,5}`. |
| IV binding on every message start | Enforced — `msg_start · (h_in[j] − IV[j]) = 0`, both limbs, for `j ∈ 0..8`.                                                                                                |
| Multi-block chain                | Enforced — `(enabler − msg_start) · (h_in[j] − h_out_prev[j]) = 0` on every continuation row.                                                                                |
| FIPS 180-4 §5.1.1 padding        | Enforced — (P.A) binary flags, (P.B) one-hot sums, (P.C/C') aux flags, (P.D) marker-word byte assembly, (P.E) `0x80` marker pin, (P.F/G) post-marker zeros, (P.H) bit length.|
| LogUp closure / soundness gate   | Enforced — every wired channel balances; `verify_sha256_proof` rejects any non-zero `interaction_claim.total()` before running Stwo's verifier.                            |

The direct AIR constraints have total degree at most 3.
The main SHA evaluator uses `max_constraint_log_degree_bound = log_size + 2`
for its degree-five batched LogUp recurrence. The prover owner also accounts
for the fixed log-16 range table, taking `max(17, log_size + 2)` outside the shared-table path.
The chain gate uses one `(enabler − msg_start)` factor.

## What this crate does **not** do

- **Bind the digest as a cryptographic public input.** The standalone facade
  proves trace validity; callers that need a public digest must bind it through
  the keyed digest relation and a consuming component.
- **Bind the bit length and marker position to the mdoc parser.**
  The padding layer constrains `W[14]` and `W[15]` to a committed length value.
  The integration layer must bind that length to the mdoc preimage.
- **Hide the witness.** This crate produces succinct, transparent proofs.
  It does not apply proof-wide zero-knowledge masking.
- **Provide a CLI.** Use `examples/prove_demo.rs` for the standalone component.
  The integration layer owns `bin/eu-id`.
- **Use the workspace range tables directly.** The local `Range_k` tables are in
  [`src/tables_local.rs`](src/tables_local.rs).
  Their function names match the planned shared exports.

## Layout

| Module              | Role                                                                                                                          |
| ------------------- | ----------------------------------------------------------------------------------------------------------------------------- |
| `constants`         | `K[0..63]` round constants and the `IV` initial hash value.                                                                   |
| `types`             | Word ↔ M31-limb representation, witness records.                                                                              |
| `headroom`          | Machine-checked M31 headroom audit for every mod-2³² add family, plus the `Range_2/4/5` carry-range bounds the AIR consumes.  |
| `native`            | Pure SHA-256 reference (padding, schedule, compression). Tested against the `sha2` crate.                                     |
| `relations`         | Active `Range_k` and integration LogUp relation tags.                                                                         |
| `tables_local`      | Local fallback for the shared `Range_k` tables (one-import-swap migration target).                                            |
| `witness`           | Full witness emitter — every value the trace stores per row.                                                                  |
| `trace`             | Column layout + materialisation from a witness.                                                                               |
| `multiplicities`    | Per-row multiplicity vectors for the active `Range_k` tables.                                                                  |
| `preprocessed`      | Active range-table and round-selector preprocessed columns (tree[0]).                                                         |
| `components`        | Active `Range_k` producers.                                                                                                   |
| `constraints`       | The main `Sha256Eval` consumer AIR.                                                                                           |
| `interaction`       | LogUp interaction-trace generator + `InteractionClaim`.                                                                       |
| `stark`             | Public `prove_sha256` / `verify_sha256_proof` entry points.                                                                   |

## Design

See the validated [`SHA-256 AIR design`](docs/research/sha256-air-design.md).
Git history contains the original design sketch.
