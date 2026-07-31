# eu-id

This repository contains a quantum-safe TS13 identity-proof demo for the EU
Digital Identity Wallet.

The demo proves these facts in one STARK:

- A trusted ML-DSA-65 issuer signed the PID.
- The PID contains `age_over_18 = true`.
- The PID is valid at the verifier timestamp.
- The holder used the device key from the PID.
- The PID is not revoked in the verifier epoch.

The native SDK has one identity path:

```rust
prove_identity(statement, witness)
verify_identity(statement, proof)
```

UniFFI generates the Kotlin and Swift names `proveIdentity` and
`verifyIdentity`.

## Privacy

The privacy claim is:

```text
public-input unlinkable; transcript zero knowledge pending
```

The public statement and proof length do not contain a credential-stable
identifier. A fresh presentation context changes the public statement.

STWO is transparent and is not zero knowledge. The proof transcript can expose
witness-derived data. Do not claim complete unlinkability or zero knowledge.

## Status

This code is for a demonstration. It is not audited and is not
production-ready. It supports one fixed PID shape and one claim. It does not
provide production PKI, wallet integration, or STWO witness masking.

The normative demo profile is
[docs/ts13-unlinkable-age18-demo-spec.md](docs/ts13-unlinkable-age18-demo-spec.md).

## Workspace

- `crates/air-core` composes the AIR modules into one STARK.
- `crates/stwo-sha256` proves SHA-256 computations.
- `crates/stwo-keccak` supplies the shared Keccak service.
- `crates/stwo-mldsa` proves ML-DSA-65 verification.
- `crates/eu-id-prover` implements the fixed TS13 circuit.
- `crates/sdk` exposes the two identity functions through UniFFI.
- `crates/sdk/android` builds the Android AAR.
- `mobile/EuIdBenchAndroid` supplies the Android instrumentation host.

## Development

Use the Rust toolchain in `rust-toolchain.toml`.

```bash
make build
make test
make check
make check-quantum-only-deps
```

All proof tests must use a release build. Run one expensive test at a time.
`--test-threads=1` serializes the test harness. The prover still uses the 12
Rayon workers selected by `RAYON_NUM_THREADS=12`.

```bash
RAYON_NUM_THREADS=12 \
RUST_MIN_STACK=536870912 \
cargo test --locked --release -p sdk --test ts13_e2e \
  -- --test-threads=1
```

Build the Android AAR from `crates/sdk/android`:

```bash
cd crates/sdk/android
./gradlew assembleRelease
```

There is no repository license file.
