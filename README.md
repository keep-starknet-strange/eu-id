# eu-id

STARK-based zero-knowledge proofs for the EU Digital Identity Wallet — a research
prototype showing that STARKs can do privacy-preserving selective disclosure on a
signed identity credential (prove *"over 18"* and *"nationality in an accepted
set"* without revealing the date of birth or nationality).

It is a concrete contribution to the EU's *Topic G* zero-knowledge technology
decision for the Digital Identity Wallet.

## Status

**This code is not audited and is not production-ready.** It is a research
prototype. The first iteration produces **succinct** proofs (small, fast to
verify) but not yet **zero-knowledge** proofs (witness masking is a deferred
follow-on), and uses a **simplified signed credential** rather than a full ISO
mdoc — both disclosed honestly.

The cryptographic components are built and individually sound:

- **ECDSA P-256 verification** — full in-circuit verification of `(z, r, s, Q)`
  with public-input binding; real arbitrary signatures prove and verify.
- **SHA-256** — multi-block hashing with padding/IV/carry constraints and a
  constraint-level negative-test suite.
- **Predicates** — age-over-18 (two strategies) and nationality set-membership.

These compose into one `StarkProof` via the `air-core` orchestration layer,
**cross-bound** to a *single* credential: the combined proof attests that a
signature verifies over the hash of the credential whose date of birth /
nationality satisfy the predicates (the global LogUp balance cancels only when
`z == SHA-256(C)` and the predicates' attributes are the credential's signed
bytes). The relying-party API (`prove_identity` / `verify_identity`) and an
`eu-id` prove/verify CLI are in place, with an end-to-end soundness suite
(one negative per mutation class) guarding the composition.

## Workspace

- `crates/stwo-p256` — ECDSA P-256 verification AIR, native reference, fake-GLV
  scalar-mul, range checks, and the proof/composition surface.
- `crates/stwo-p256-utils` — prover-independent limb/Solinas/scalar arithmetic and
  the M31 headroom audit.
- `crates/stwo-sha256` — SHA-256 AIR (M31 lookup-table design). See
  `crates/stwo-sha256/docs/research/sha256-air-design.md`.
- `crates/predicates` — age-over-N and nationality-in-set predicates, with
  `prove`/`verify` CLI binaries. See `crates/predicates/USAGE.md`.
- `crates/air-core` — composes `Air`/`AirProver` modules into one STARK proof
  under a single channel, commitment scheme, and global LogUp balance.
- `crates/eu-id-prover` — the end-to-end combined prover built on `air-core`;
  exposes `prove_identity` / `verify_identity` and the `eu-id` prove/verify CLI.
- `crates/eu-id-ffi` — C-ABI surface for the mobile benchmark harness (`mobile/`).

## Development

Use the pinned Rust toolchain from `rust-toolchain.toml`.

```bash
cargo check
cargo test
cargo clippy --all-targets --all-features
make check      # CI-equivalent: clippy -D warnings + fmt --check
```

## Benchmarks

End-to-end performance numbers for the combined identity proof — per-component
breakdown (P256, SHA, age, nationality), the full pipeline, prove/verify time,
proof size, and peak memory — are in `docs/benchmarks.md`, with machine-readable
results under `docs/benchmarks/`.

```bash
make bench          # criterion timing (per-stage + full pipeline)
make bench-report   # peak-memory + proof-size JSON report
```

The mobile harness (`mobile/EuIdBench`) runs the same combined prover on-device
via the FFI surface; see `docs/benchmarks.md` for the device repro.

There is currently no repository license file.
