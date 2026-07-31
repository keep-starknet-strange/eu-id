# TS13 `proveIdentity` Firebase Test Lab benchmark

Date: 2026-07-30

Firebase Test Lab ran one cold process on each physical device.
The test used `IdentityStatement` and `IdentityWitness`.
The test called `proveIdentity`.
The test checked the identity-proof envelope.
The test then called `verifyIdentity`.

## Provenance

- Source commit: `214eeaf9`
- Circuit hash:
  `fe00ac0fe17f146e5f79220d30df84768c8d8a6d8d7b778a248303f5be8b36ab`
- Android SDK AAR SHA-256:
  `cd4da38be351c66c668dd27094e96f34627c98fb2cafb02eec9f3eb9d609a5d4`
- Host APK SHA-256:
  `14680db8781ffef8219c388cd6c223eba80a02b9574721b3879b61b814f5e5aa`
- Test APK SHA-256:
  `bb0af6d2fc074a35028559a56abe3c1dc47e2413b1398e48b3ca39c9e7ed7696`
- Fixture SHA-256:
  `8993dcf9484ee950db0f06e3be0be9402e8b9ca0e11576446fe2bc3c5c4a13f9`
- Firebase project: `exploration-dev-417917`
- Matrix ID: `matrix-9779illjtcvba`
- Android version: Android 14, API 34
- Test:
  `com.kss.euid.zk.sdk.Ts13MobileBenchmarkInstrumentedTest#proveIdentity_emitsBenchmarkResult`
- [Firebase results](https://console.firebase.google.com/project/exploration-dev-417917/testlab/histories/bh.a21b73b77a063202/matrices/4979366871595643398)

## Results

| Device | Processors | Prove | Verify | Identity-proof envelope | Peak resident memory |
| --- | ---: | ---: | ---: | ---: | ---: |
| Samsung Galaxy S24 Ultra (`SM-S928U1`) | 8 | 4,081 ms | 214 ms | 1,769,518 bytes | 2,094,228 KiB |
| Google Pixel 8 | 9 | 7,892 ms | 257 ms | 1,769,518 bytes | 2,030,844 KiB |
| Samsung Galaxy A54 5G (`SM-A546U`) | 8 | 11,601 ms | 333 ms | 1,769,518 bytes | 2,015,544 KiB |

All three tests passed.
The Android runtime reported the processor count.
The default Rayon pool used the available processors.
The test read peak resident memory from `VmHWM` in `/proc/self/status`.

Each result is one sample.
The results do not define a stable performance distribution.
Peak resident memory was approximately 2 GiB.
An integrated wallet can use more memory than this isolated test.
