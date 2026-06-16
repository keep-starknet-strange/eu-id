# eu-id

Research prototype for a P-256 ECDSA verification AIR built on Stwo.

## Status

This code is not audited and is not production-ready.

The implemented proof-facing slice is currently the scalar modular multiplication AIR under
`crates/stwo-p256/src/scalar/scalar_mod_mul`, with Falcon-style trace/debug wiring in
`crates/stwo-p256/src/debug`. The full end-to-end ECDSA proof API is intentionally not exposed
until public input binding, scalar setup wiring, elliptic-curve transition components, and proof
orchestration are implemented.

## Workspace

- `crates/stwo-p256`: AIR-facing code, native witnesses, range-check providers, scalar setup, and scalar mod-mul components.
- `crates/stwo-p256-utils`: prover-independent arithmetic utilities, limb constants, scalar arithmetic traces, and Solinas matrix generation.
- `crates/stwo-p256/docs`: implementation specs for the P-256 ECDSA AIR.
- `crates/predicates`: STARK proofs for credential predicates (age-over-N and nationality-in-set), with an orchestrator that combines proving modules into a single STARK proof, plus `prove`/`verify` CLI binaries. See `crates/predicates/USAGE.md`.

## Development

Use the pinned Rust toolchain from `rust-toolchain.toml`.

```bash
cargo check
cargo test
cargo clippy --all-targets --all-features
```

There is currently no repository license file.
