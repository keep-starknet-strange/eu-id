# eu-id

Quantum-safe STARK proofs for the EU Digital Identity Wallet — a research
prototype for privacy-preserving selective disclosure from an ISO/IEC 18013-5
PID mdoc.

It is a concrete contribution to the EU's *Topic G* zero-knowledge technology
decision for the Digital Identity Wallet.

## Status

**This code is not audited and is not production-ready.** It is a research
prototype. The first iteration produces **succinct** proofs (small, fast to
verify) but not yet **zero-knowledge** proofs (witness masking is a deferred
follow-on). The product path uses ML-DSA-65 for issuer, device, and revocation
authentication. Classical P-256 implementations and parity benchmarks live on
their dedicated branches.

The cryptographic components are built and individually sound:

- **ML-DSA-65 verification** — issuer, device, and revocation signatures are
  verified in-circuit through a shared SHAKE-256 service.
- **SHA-256** — multi-block hashing with padding/IV/carry constraints and a
  constraint-level negative-test suite.
- **Predicates** — age-over-18 (two strategies) and nationality set-membership.

These compose into one `StarkProof` via the `air-core` orchestration layer,
**cross-bound** to a *single* mdoc presentation: issuer auth, ISO device auth,
MSO digest membership, device-key origin, credential validity, and the
age/nationality predicates are bound in the mdoc proof. The product Rust API is
`eu_id_prover::{prove_mdoc, verify_mdoc}` and the SDK product API is
`prove_mdoc_pid` / `verify_mdoc_pid`.

## Workspace

- `crates/stwo-mldsa` — ML-DSA-65 verification AIR and native reference.
- `crates/stwo-keccak` — shared SHAKE-256/Keccak service used by the ML-DSA
  instances.
- `crates/stwo-sha256` — SHA-256 AIR (M31 lookup-table design). See
  `crates/stwo-sha256/docs/research/sha256-air-design.md`.
- `crates/predicates` — age-over-N and nationality-in-set predicates, with
  `prove`/`verify` CLI binaries. See `crates/predicates/USAGE.md`.
- `crates/air-core` — composes `Air`/`AirProver` modules into one STARK proof
  under a single channel, commitment scheme, and global LogUp balance.
- `crates/eu-id-prover` — the end-to-end quantum-safe mdoc prover built on
  `air-core`.
- `crates/sdk` — UniFFI-facing SDK contract and product mdoc PID proof
  envelope (`prove_mdoc_pid` / `verify_mdoc_pid`).
- `crates/eu-id-ffi` — C-ABI surface for the mobile benchmark harness (`mobile/`).

## Development

Use the pinned Rust toolchain from `rust-toolchain.toml`.

```bash
cargo check
cargo test
make check      # CI-equivalent: clippy -D warnings + fmt --check
make check-quantum-only-deps
```

## Benchmarks

The metric of record is the full quantum-safe mdoc proof in a single-threaded
release build. The S1-S9 campaign record and proof-size breakdown are in
`tasks/keccak-service-design.md`.

```bash
make perf
```

There is currently no repository license file.
