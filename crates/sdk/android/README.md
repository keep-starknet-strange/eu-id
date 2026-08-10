# EU-ID identity proof SDK for Android

This Gradle project packages the Rust SDK as an Android AAR. The AAR contains
the UniFFI Kotlin bindings and the native library for each supported ABI. The
published Maven package declares JNA as a transitive dependency.

The wallet-facing proof API uses tagged statements and witnesses:

- `proveIdentity(ZkPublicStatement, ZkMdocWitness): ByteArray`
- `verifyIdentity(ZkPublicStatement, ByteArray): ZkVerifyResult`

For the TS13 proof, wrap the identity records in their `Ts13DemoV1`
variants and check the verification result:

```kotlin
val publicStatement = ZkPublicStatement.Ts13DemoV1(identityStatement)
val privateWitness = ZkMdocWitness.Ts13DemoV1(identityWitness)
val proof = proveIdentity(publicStatement, privateWitness)
check(verifyIdentity(publicStatement, proof).ok)
```

The demo wallet flow also uses `demoIssuerPublicKey`,
`demoRevocationPublicKey`, `demoRevocationEpoch`, `demoRevocationWitness`,
`demoMintMlDsaSignedPidMdoc`, `demoDeviceAuthSigStructure`, and
`demoBuildMlDsaWitness`.

The SDK uses six proof workers. It sets the proof-thread stack to 2 MiB and
each worker stack to 16 MiB. The public API has no runtime controls.

The Maven coordinate is `com.kss:eu-id-zk-sdk:0.1.0`. The Kotlin
package is `com.kss.euid.zk.sdk`.

From the repository root, `make publish-local` publishes that AAR and the
matching host-test JAR, `com.kss:eu-id-zk-sdk-jvm:0.1.0`, to `mavenLocal()`.

## Prerequisites

Install these tools:

- JDK 17 or later
- Android SDK 36
- The NDK version in `build.gradle.kts`
- `cargo-ndk`
- The Rust targets `aarch64-linux-android` and `x86_64-linux-android`

Set `ANDROID_HOME` or `ANDROID_SDK_ROOT`. You can also put `sdk.dir` in
`local.properties`.

## Build

Run these commands from this directory:

```bash
./gradlew assembleRelease
./gradlew publishToMavenLocal
```

The build uses the Rust release profile. It creates the native libraries before
it creates the Kotlin bindings and the AAR. Set `-PndkVersion=<version>` only
when you must use a different installed NDK.

Use these tasks for a partial build:

- `cargoNdkBuild` builds the native libraries.
- `generateUniffiBindings` creates the Kotlin bindings.
- `assembleRelease` creates the AAR.

## Firebase benchmark

The benchmark host is in `mobile/EuIdBenchAndroid`. Build the current AAR
first. Then run this command from the repository root:

```bash
./crates/sdk/android/gradlew -p mobile/EuIdBenchAndroid \
  assembleRelease assembleReleaseAndroidTest \
  -Pts13SdkAar=/absolute/path/to/euid-zk-sdk-release.aar
```

Upload these files to Firebase Test Lab:

- `mobile/EuIdBenchAndroid/build/outputs/apk/release/EuIdBenchAndroid-release.apk`
- `mobile/EuIdBenchAndroid/build/outputs/apk/androidTest/release/EuIdBenchAndroid-release-androidTest.apk`

Run this test target:

```text
class com.kss.euid.zk.sdk.Ts13MobileBenchmarkInstrumentedTest#proveIdentity_emitsBenchmarkResult
```

The test writes one summary and one bounded record for each proof phase with
the `Ts13MobileBenchmark` log tag. The summary contains prove time, verify
time, proof size, runtime settings, and peak process memory.

## Use the AAR

Add `mavenLocal()` to the repositories of the wallet or verifier. Then add
this dependency:

```kotlin
implementation("com.kss:eu-id-zk-sdk:0.1.0")
```

The Maven package supplies the AAR and its JNA dependency. If you use the AAR
file directly, add JNA 5.19.1 to the application.
