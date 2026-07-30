# TS13 `proveIdentity` Firebase Test Lab benchmark

This is one cold-process instrumentation execution per physical device. The
test constructs the tagged `ZkPublicStatement.Ts13DemoV1` and
`ZkMdocWitness.Ts13DemoV1` fixture, calls the generated Kotlin
`proveIdentity` API, validates the frozen V4 envelope, and calls
`verifyIdentity`.

## Provenance

- Source commit: `214eeaf9`
- Circuit hash:
  `fe00ac0fe17f146e5f79220d30df84768c8d8a6d8d7b778a248303f5be8b36ab`
- Android SDK release AAR SHA-256:
  `cd4da38be351c66c668dd27094e96f34627c98fb2cafb02eec9f3eb9d609a5d4`
- Host APK SHA-256:
  `14680db8781ffef8219c388cd6c223eba80a02b9574721b3879b61b814f5e5aa`
- Instrumentation APK SHA-256:
  `bb0af6d2fc074a35028559a56abe3c1dc47e2413b1398e48b3ca39c9e7ed7696`
- Fixture SHA-256:
  `8993dcf9484ee950db0f06e3be0be9402e8b9ca0e11576446fe2bc3c5c4a13f9`
- Firebase project: `exploration-dev-417917`
- Matrix ID: `matrix-9779illjtcvba`
- Test axis API level: Android 14 / API 34
- Test target:
  `com.kss.euid.zk.sdk.Ts13MobileBenchmarkInstrumentedTest#proveIdentity_ts13DemoV1_emitsBenchmarkResult`
- Results:
  <https://console.firebase.google.com/project/exploration-dev-417917/testlab/histories/bh.a21b73b77a063202/matrices/4979366871595643398>

## Results

| Firebase axis | Reported model | Processors | Prove | Verify | V4 envelope | `VmHWM` |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `e3q-34-en-portrait` | Samsung Galaxy S24 Ultra (`SM-S928U1`) | 8 | 4,081 ms | 214 ms | 1,769,518 bytes | 2,094,228 KiB |
| `shiba-34-en-portrait` | Google Pixel 8 | 9 | 7,892 ms | 257 ms | 1,769,518 bytes | 2,030,844 KiB |
| `a54x-34-en-portrait` | Samsung Galaxy A54 5G (`SM-A546U`) | 8 | 11,601 ms | 333 ms | 1,769,518 bytes | 2,015,544 KiB |

All three axes passed. `available_processors` is reported by the Android
runtime and the SDK's default Rayon pool uses that available parallelism.
`VmHWM` is read from `/proc/self/status` after verification and represents
the process high-water resident memory, not a heap-only measurement.

These are single samples intended to establish physical-device viability,
not statistically stable performance distributions. The principal demo risk
is the roughly 2 GiB process high-water mark; integrated-wallet memory
pressure can differ from this isolated benchmark.
