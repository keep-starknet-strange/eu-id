# eu-id

`eu-id` is a research implementation of a private identity proof for an EU
Digital Identity Wallet. The sole product path uses classical P-256 and
SHA-256. It proves claims from an ISO mdoc without moving the private claim
checks into the application.

This code is not production-ready. The proof is transparent. STWO does not yet
provide transcript-wide zero knowledge, so this repository does not claim that
the complete proof hides every witness value. Transcript-wide zero knowledge is
future work.

## Product contract

Applications use the UniFFI `proveIdentity` and `verifyIdentity` functions.
The corresponding Rust functions are `prove_identity` and `verify_identity` in
`crates/sdk`. No other identity-proof application flow is supported.

The SDK emits one V8 envelope. Its fixed-width body contains only:

- `version = 8`
- one zstd-compressed STARK proof

The verifier does not accept a statement from the proof. It validates the
caller statement and reconstructs every public circuit input. The statement
pins the product profile, circuit source, root policy, issuer P-256 key,
revocation key and epoch, UTC verification time, session transcript, and claim
policy.

The current credential profile accepts the PID 2.0 forms used by this product:

- `birth_date` is a CBOR tag-1004 `YYYY-MM-DD` text value.
- `nationality` is a nonempty array of ISO alpha-2 text values. The signed
  domain also permits `QU` and `QS`, as required by the PID Rulebook.
- A verifier nationality policy contains only assigned ISO alpha-2 codes.

The proof enforces these checks together:

- The issuerAuth ES256 signature verifies under the exact caller-authorized
  P-256 key. The singleton x5chain leaf contains that same key.
- The signed MSO and each requested IssuerSignedItem have the required CBOR and
  SHA-256 bindings. Digest identifiers are unique.
- The hidden device key comes from the MSO and verifies DeviceAuthentication
  for the caller session transcript and document type.
- Signed validity satisfies `validFrom < now < validUntil` at the caller UTC
  time.
- The private birth date satisfies the requested age threshold.
- Every signed nationality is valid, and at least one satisfies the requested
  accepted set when that predicate is active.
- The MSO-derived revocation identifier is strictly inside the signed
  revocation interval for the caller key and epoch.

## Workspace

- `crates/sdk` provides the application contract, V8 envelope, UniFFI exports,
  and Android benchmark adapter.
- `crates/eu-id-prover` parses the supported mdoc and composes the product
  proof.
- `crates/eu-id-ec-coprocessor` proves the P-256 equality subprotocol.
- `crates/stwo-p256` and `crates/stwo-p256-utils` implement the P-256 AIR and
  arithmetic support.
- `crates/stwo-sha256` implements the SHA-256 AIR.
- `crates/predicates` implements the private age and nationality relations.
- `crates/air-core` composes the STWO modules and shared relations.
- `crates/eu-id-ffi` exposes only the standalone SHA-256 and P-256 C benchmark
  functions.

## Build and test

The repository pins its Rust nightly in `rust-toolchain.toml`. Release builds
use fat LTO and one code-generation unit. The commands default to 12 Cargo and
Rayon workers. Proof-heavy tests use one test thread.

```bash
make check
make build
make test
make test-ignored
```

`make check` runs release Clippy, rustfmt, locked dependency metadata, artifact
drift, and shell syntax checks. `make check-reproducible` builds the shipped SDK
library types and identity probe in two distinct target directories, then
compares their bytes. Set `ALLOW_DIRTY=1` only when a deliberately dirty audit
build must carry source provenance.

Regenerate source-bound product pins after an intentional circuit change:

```bash
python3 scripts/product_profile_artifacts.py
python3 scripts/product_profile_artifacts.py --check
```

## Benchmarks and mobile builds

```bash
make bench-identity    # exact proveIdentity / verifyIdentity API
make bench-components  # standalone SHA-256 and P-256 C ABI
make bench-mobile      # Android product benchmark APK
```

The Android SDK project is in `crates/sdk/android`. It builds arm64-v8a and
x86_64 libraries and packages the generated UniFFI Kotlin bindings in one AAR.
The benchmark APK is in `mobile/EuIdBenchAndroid`. The iOS component harness is
in `mobile/EuIdBench`.

There is no repository license file.
