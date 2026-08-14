# eu-id-zk-sdk (Android)

This module packages the Rust `sdk` crate as an Android AAR.
The AAR contains UniFFI Kotlin bindings and one native library for each ABI.
It also contains the JNA runtime.
Consumers add one Maven dependency.

## Coordinate

```
com.kss:eu-id-zk-sdk:0.1.0          // Kotlin package: com.kss.euid.zk.sdk
```

## How it works

The build does not use a third-party Rust Gradle plugin.
The old `rust-android-gradle` plugin cannot run on Gradle 9.
Two Gradle tasks run `cargo-ndk` and `uniffi-bindgen`:

- `cargoNdkBuild` cross-compiles `libeuid_zk_sdk.so` for each ABI.
- `generateUniffiBindings` runs the bundled `uniffi-bindgen`.

Both tasks write below `build/generated`.
The Android Gradle Plugin variant API owns and packages these outputs.
The release build rejects a dirty Git worktree by default.
Use `-PallowDirtyBuild=true` only for an explicitly labeled local build.

## Prerequisites

- JDK 17+ and Android SDK (Android Studio supplies both).
- An installed NDK matching `ndkVersion` in `build.gradle.kts` (used by both
  cargo-ndk and AGP's release strip).
- `cargo-ndk` 4.1.2: `cargo install cargo-ndk --version 4.1.2 --locked`.
- The Android Rust targets: `rustup target add aarch64-linux-android x86_64-linux-android`.

The repository contains a Gradle 9.5.0 wrapper.
You do not need a system Gradle installation.

## Build & publish (to Maven Local)

```bash
cd crates/sdk/android
./gradlew publishToMavenLocal      # builds .so (all ABIs) + bindings + AAR -> ~/.m2
```

Useful intermediate tasks:

- `./gradlew cargoNdkBuild` — cross-compile `libeuid_zk_sdk.so` per ABI.
- `./gradlew generateUniffiBindings` — emit `com/kss/euid/zk/sdk/euid_zk_sdk.kt`.
- `./gradlew assembleRelease` — build the AAR without publishing.

## Test

**Instrumented tests** in `src/androidTest` test the SDK.
They run on an emulator or device and load the bundled native library.

```bash
# with an emulator/device connected:
./gradlew connectedAndroidTest
```

This project has no JVM unit tests in `src/test`.
They would require a separate host library for macOS or Linux.

## Consume

In the wallet / verifier build:

```kotlin
// settings.gradle.kts (or root build) repositories:
repositories { mavenLocal(); google(); mavenCentral() }

// module build.gradle.kts:
dependencies { implementation("com.kss:eu-id-zk-sdk:0.1.0") }
```

```kotlin
import com.kss.euid.zk.sdk.proveIdentity
import com.kss.euid.zk.sdk.verifyIdentity
// ... ZkPublicStatement, ZkMdocWitness, ZkVerifyResult, PredicateMode,
// ZkException, and the product pin functions
```

`ZkPublicStatement` carries the verifier-authoritative P-256 issuer coordinates
as `issuerPublicKeyX` and `issuerPublicKeyY`. It carries the canonical CBOR
SessionTranscript as `sessionTranscript`. Nationality policies use a sorted,
unique list of uppercase ISO 3166-1 alpha-2 strings in
`acceptedAlpha2Countries`. The signed mdoc must contain exactly one x5chain
leaf. Its SubjectPublicKeyInfo P-256 key must equal the verifier-authoritative
coordinates.

JNA and the native libs arrive transitively inside the AAR.
