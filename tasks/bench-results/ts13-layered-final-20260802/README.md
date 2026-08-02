# TS13 layered final-hash evidence

Date: 2026-08-02

Status: The soundness review, release tests, Android package, and desktop
campaign are complete. The final Firebase run waits for `A-014-confirmed`.

Privacy claim: `public-input unlinkable; transcript zero knowledge pending`

STWO is not zero knowledge. This campaign does not add transcript masking.

## Provenance

- Branch: `codex/ts13-unlinkable-v1`
- Soundness-source commit: `cf8f2cec27f7952d982c6d157a7fb3793ee79010`
- Artifact and fixture commit: `c2923bac3823d6763d425e2049793b3513247975`
- Circuit hash:
  `c7c99e7b6e7cddbfc27617b2597bea1315ebd39e34ed08c564d67220282af9bc`
- Soundness source-tree SHA-256:
  `1dd43881cc9444187a6b21dcfa3634acd13be2d8e334438a2169d4c67dcb2e55`
- Shape manifest SHA-256:
  `a1fbcd6e451f13cbf864a5b1897eb5eb3aba24bbeaed52e2c8c22ceeda612cee`
- Generation input SHA-256:
  `d8bd7239714d021cec28c87f00c9603e5d3098524e3c3c21b68af125aee429e4`
- Cargo lock SHA-256:
  `220b0810dc0423085bb2654fd738ee5d0ee71ca8e61cf971ae38edc128ff87ff`
- Rust toolchain file SHA-256:
  `8f0604004d13f7a26332366e59ba731bbb6046aaf789439d760abf67ad78589f`
- Release probe SHA-256:
  `18a57471b4dacc780b3f0b7f35c7b7457e82d7eaab1f0ce878263d3d3b222076`
- Proof-body capacity: 1,507,328 bytes
- Identity-proof envelope: 1,507,374 bytes

The artifact keeps the same shape and capacity as the reviewed candidate.
The F-2 source change rotates only the source digest and circuit identity.

## Review conditions

A-015-review accepted the layered protocol as sound. It reported no critical
or high finding. This checkpoint completes its three conditions:

1. The design states the actual source-tree and payload-shape bindings.
2. Exported `verifyIdentity` rejects a committed `low + 256`, `high - 1`
   nibble pair. The malicious prover emits an encoded proof first.
3. The design states that no live source recomputes the removed carrier's
   `8974/q` value. Acceptance does not depend on that value.

The exact F-2 release test returned `ProofVerificationFailed`. It did not
return a host, envelope, or prover error. The verifier failed in the layered
extraction sumcheck. The honest verifier code did not change.

## Release verification

The final circuit passed these checks:

- Workspace release check for all targets.
- Workspace release Clippy with warnings denied.
- All normal release tests with one harness thread.
- All 18 ignored release tests.
- The exact A1/A2/B unlinkability test.
- The exact 17-case exported `proveIdentity` rejection matrix.
- The exact exported `verifyIdentity` off-domain nibble negative.
- All three live composed-artifact tests.
- The 30-test layered Keccak freeze.
- The 31-test Keccak service freeze.
- The exact public API schema test.
- The exact committed-source artifact test and direct artifact check.
- The quantum-only dependency check.
- Formatting and the clean-diff check.

Each proof test used one test-harness thread. Proof work used the configured
parallel runtime. The product `proveIdentity` path used its fixed six-worker
pool, 2 MiB proof-thread stack, and 16 MiB worker stack.

## Android package

Local package root:
`/private/tmp/euid-ts13-final-c7c99e7b-20260802-1/package`

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| AAR | 6,480,618 | `7cfae6f366c3227c3dd99607589c624b0f013a6ec1722bfc29746697545ce742` |
| Host APK | 17,918,890 | `888c7a298e996f9edc47bac9b95507a52611ece54de9544f50b52d033eb27fdd` |
| Test APK | 704,395 | `1699917f54f2a1e3db8eb9d9a04b7297f3bd6b3ebf66c0cca8323d6e649b7f5f` |
| Fixture | 40,035 | `e5fc8f6b6b378bfb6e5ebf72ef9a744c13458dd23ec11aebef08fdc60bc9dbc1` |
| ARM64 library | 6,598,032 | `182d6c22c0ab6e0b0d90a8cf7e358864b948eb323b55e2efbecacbf248bcef5f` |

The AAR and host APK contain the same stripped AArch64 library. The test APK
contains the exact generated fixture. The fixture binds the final circuit
hash and names only `proveIdentity` and `verifyIdentity`. The generated Kotlin
API exposes those two application proof functions.

## Desktop method

The host was a 12-core Apple M2 Max MacBook Pro with 32 GB of memory. It ran
macOS 26.5.2, build 25F84. The compiler was Rust nightly 1.94.0 from
2026-01-14.

Each sample used a fresh process and one `proveIdentity` call. The benchmark
invoked the release binary directly. `/usr/bin/time -l` measured the process
peak resident set size. Each process wrote 25 valid phase records to a new
file. The phase row for the median proving sample is in `desktop-phases.csv`.

## Desktop results

| Metric | Result |
| --- | ---: |
| Samples | 7 |
| Median prove | 1,780 ms |
| Median verify | 81 ms |
| Median peak RSS | 780,435,456 bytes |
| Maximum peak RSS | 786,415,616 bytes |
| Envelope | 1,507,374 bytes |

The complete process results are in `desktop-cold.csv`. Compared with the
reviewed pre-F-2 checkpoint, the prove median is 4 ms lower and the verify
median is 1 ms higher. The maximum RSS is 8,732,672 bytes higher. These small
differences do not show an honest-path performance change.

## Pending phone gate

Firebase must run the same host and test APKs on Pixel 8 (`shiba`), Galaxy S24
Ultra (`e3q`), and Galaxy A54 (`a54x`) with API 34. One matrix must run all
three phones in parallel. The binding gates are:

- Cold `proveIdentity` below 2,000 ms on each phone.
- `verifyIdentity` at most 500 ms on each phone.
- A fixed envelope below 2,500,000 bytes.
- Exactly 25 phase records and the fixed runtime settings.

The upload remains on hold until the mailbox contains `A-014-confirmed`.
