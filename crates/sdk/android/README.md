# eu-id-zk-sdk (Android)

Packages the `sdk` Rust crate into a plug-and-play Android AAR: the UniFFI Kotlin
bindings, the native `libeuid_zk_sdk.so` for each ABI, and the JNA runtime — all
behind a single Maven coordinate. Consumers (wallet `:zkp-logic`, the verifier's Android
`actual`) add one dependency line; nothing is copied or hand-wired.

## Coordinate

```
com.kss:eu-id-zk-sdk:0.1.0          // Kotlin package: com.kss.euid.zk.sdk
```

## How it works

No third-party Rust/Gradle plugin (the stale `rust-android-gradle` plugin can't
run on Gradle 9). Two plain Gradle `Exec` tasks drive cargo-ndk + uniffi-bindgen
directly:

- `cargoNdkBuild` — `cargo ndk` cross-compiles `libeuid_zk_sdk.so` per ABI into `src/main/jniLibs/`.
- `generateUniffiBindings` — runs the bundled `uniffi-bindgen` into `src/main/kotlin/`.

`preBuild` depends on both; writing into AGP's conventional source dirs means
they're packaged into the AAR with no source-set DSL. Runs on Gradle 9.x.

## Prerequisites

- JDK 17+ and Android SDK (Android Studio supplies both).
- An installed NDK matching `ndkVersion` in `build.gradle.kts` (used by both
  cargo-ndk and AGP's release strip).
- `cargo-ndk`: `cargo install cargo-ndk`.
- The Android Rust targets: `rustup target add aarch64-linux-android x86_64-linux-android`.

The Gradle wrapper is committed (`./gradlew`, pinned to Gradle 9.5.0), so no
system Gradle install is needed — `./gradlew` bootstraps it.

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

The SDK is exercised by **instrumented tests** (`src/androidTest`), which run on
an emulator/device and load the bundled ABI `.so` — no host-arch build needed.

```bash
# with an emulator/device connected:
./gradlew connectedAndroidTest
```

(JVM unit tests under `src/test` are not used: they'd load the library from the
host and so would require a separate macOS/Linux `libeuid_zk_sdk` build.)

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
// ... ZkPublicStatement, ZkWitness, ZkVerifyResult, PredicateMode, NatMode, ZkException
```

JNA and the native libs arrive transitively inside the AAR.
