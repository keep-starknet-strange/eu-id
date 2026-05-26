# stwo-sha256

SHA-256 STARK AIR over the M31 field for the `eu-id` credential pipeline,
built on [Stwo](https://github.com/starkware-libs/stwo).

> **Status — research prototype.** Not audited; not zero-knowledge yet (the
> proof is succinct only). See the workspace [`README`](../../README.md)
> for the broader project context and the public-research framing.

## What this crate proves

Given a private message `m`, `prove_sha256(m, &ProverConfig::default())`
produces a STARK proof that the committed trace is a valid SHA-256
computation of *some* preimage, with every intermediate (the 64 schedule
words `W[t]`, every round's working state, every block's `h_in` / `h_out`,
the FIPS 180-4 §5.1.1 padding, and the multi-block chain) enforced by the
AIR's constraint layer. Cross-component binding of the digest output to
external public inputs (the mdoc `valueDigests` membership and the COSE
`Sig_structure` digest → ECDSA `z`) is the integration layer's job and is
intentionally outside the scope of this standalone component.

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

The release-mode round-trip is `#[ignore]`d by default because the 2²¹-row
packed Maj/Ch preprocessed-table generation dominates wall time. Run it
explicitly with `--ignored` (above) or via `make`.

## What the AIR enforces today

| Soundness obligation             | Status                                                                                                                                                                      |
| -------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Every 16-bit limb in `[0, 2¹⁶)` | Enforced — round-side / σ-side split-and-pack lookups pin most limbs implicitly; terminal `h_out` limbs are pinned by an explicit `Range_16` lookup.                        |
| Every mod-2³² limb-add identity | Enforced — schedule recurrence, `T1`, `T2`/`e_new`/`a_new`, and the 8 finalization adds emit linear constraints **and** range-check their carries against `Range_{2,4,5}`. |
| IV binding on the first block    | Enforced — `is_first_block · (h_in[j] − IV[j]) = 0`, both limbs, for `j ∈ 0..8`.                                                                                            |
| Multi-block chain                | Enforced — `(enabler − is_first_block) · (h_in[j] − h_out_prev[j]) = 0` on every continuation row.                                                                          |
| FIPS 180-4 §5.1.1 padding        | Enforced — (P.A) binary flags, (P.B) one-hot sums, (P.C/C') aux flags, (P.D) marker-word byte assembly, (P.E) `0x80` marker pin, (P.F/G) post-marker zeros, (P.H) bit length.|
| LogUp closure / soundness gate   | Enforced — every wired channel balances; `verify_sha256_proof` rejects any non-zero `interaction_claim.total()` before running Stwo's verifier.                            |

The constraint degree stays at 2 throughout (`max_constraint_log_degree_bound
= log_size + 1`); the §10.3 chain gate uses the single-factor
`(enabler − is_first_block)` form to avoid pushing degree to 3.

## What this crate does **not** do

- **Bind the digest as a cryptographic public input.** `Sha256Proof::digest`
  is witness-derived metadata, **not** a verifier-checked input. The
  standalone verifier never mixes `digest` into its channel and never
  compares it to the trace's `h_out` columns. Digest binding via two
  LogUp relations (`valueDigests`, ECDSA `z`) lands with the integration
  layer.
- **Tie the bit-length / marker position to the mdoc parser.** The padding
  layer constrains `W[14]`/`W[15]` to a length value committed in dedicated
  aux columns, but binding that length to the mdoc preimage waits for
  roadmap 2.4 (mdoc/COSE structure analysis).
- **Hide the witness.** This crate produces *succinct* proofs, not
  zero-knowledge ones. ZK masking is roadmap 4.1.
- **Ship a CLI.** `examples/prove_demo.rs` is the shortest path today; the
  real `bin/eu-id` is owned by the integration stream.
- **Use the workspace-shared range-check tables directly.** Until
  `stwo-p256-utils` (branch `origin/lucas/p256`) lands on `main`, the four
  `Range_k` tables live in [`src/tables_local.rs`](src/tables_local.rs)
  with the *exact* function names the shared crate will export — migration
  is a one-import swap at every call site.

## Layout

| Module              | Role                                                                                                                          |
| ------------------- | ----------------------------------------------------------------------------------------------------------------------------- |
| `constants`         | `K[0..63]` round constants and the `IV` initial hash value.                                                                   |
| `partitions`        | Validated bit-index partitions for `Σ0` / `Σ1` / `σ0` / `σ1` (see `research/sha256-air-design.md`).                            |
| `types`             | Word ↔ M31-limb representation, witness records.                                                                              |
| `headroom`          | Machine-checked M31 headroom audit for every mod-2³² add family, plus the `Range_2/4/5` carry-range bounds the AIR consumes.  |
| `native`            | Pure SHA-256 reference (padding, schedule, compression). Tested against the `sha2` crate.                                     |
| `relations`         | LogUp relation tags: σ/Σ decode (8) + Maj/Ch + `xor_8` + split-and-pack (8) + `Range_k` (4).                                  |
| `tables`            | Preprocessed lookup-table content (decode, packed Maj/Ch, `xor_8`, split-and-pack).                                           |
| `tables_local`      | Local fallback for the shared `Range_k` tables (one-import-swap migration target).                                            |
| `witness`           | Full witness emitter — every value the trace stores per row.                                                                  |
| `trace`             | Column layout + materialisation from a witness.                                                                               |
| `multiplicities`    | Per-row LogUp multiplicity vectors per lookup table.                                                                          |
| `preprocessed`      | `CircleEvaluation`s for every preprocessed lookup-table column (tree[0]).                                                     |
| `components`        | `FrameworkEval` producer components for every preprocessed lookup table.                                                      |
| `constraints`       | The main `Sha256Eval` consumer AIR.                                                                                           |
| `interaction`       | LogUp interaction-trace generator + `InteractionClaim`.                                                                       |
| `stark`             | Public `prove_sha256` / `verify_sha256_proof` entry points.                                                                   |

## Design

See [`../../research/sha256-air-design.md`](../../research/sha256-air-design.md) (the
validated design, supersedes the original sketch in `docs/sha256_air_design.md`).
