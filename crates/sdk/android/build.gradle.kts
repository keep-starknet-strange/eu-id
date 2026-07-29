// Packages the `sdk` Rust crate into a plug-and-play Android AAR, with no
// third-party Rust/Gradle plugin (so it runs on Gradle 9+):
//   - cargoNdkBuild        cross-compiles libeuid_zk_sdk.so per ABI via cargo-ndk,
//   - generateUniffiBindings runs our bundled uniffi-bindgen for the Kotlin,
//   - both write into AGP's conventional source dirs (src/main/jniLibs,
//     src/main/kotlin), so they're packaged into the AAR with no source-set DSL,
//   - JNA is `api` (transitive to consumers),
//   - maven-publish ships it to the local Maven repo.
//
// Consumer side is one line — no copied .so, no manual JNA, no vendored bindings:
//   repositories { mavenLocal() }
//   implementation("com.kss:eu-id-zk-sdk:0.1.0")
//
// Versions: AGP 9.2.0 requires Gradle 9.4.1+ and JDK 17+. Kotlin support is
// BUILT IN since AGP 9.0 — the standalone org.jetbrains.kotlin.android plugin is
// no longer applied (doing so errors). See https://kotl.in/gradle/agp-built-in-kotlin
// If Android Studio ships a different AGP, let the AGP Upgrade Assistant align it.

plugins {
    id("com.android.library") version "9.2.1"
    id("maven-publish")
}

// Layout, relative to this project dir (crates/sdk/android):
//   ../        -> crates/sdk     (uniffi.toml)
//   ../../..   -> Cargo workspace root (for `cargo ... -p sdk`)
val workspaceRoot = file("$projectDir/../../..")
val crateDir = file("$projectDir/..")
val uniffiConfig = file("$projectDir/../uniffi.toml")

// Single source of truth for the published version: the Cargo workspace. Crates
// set `version.workspace = true`, so the literal lives in the root Cargo.toml
// under [workspace.package] — the same value Rust sees as CARGO_PKG_VERSION.
// Parse it here so the AAR version can never drift from the crate; bump it once
// in the Cargo manifest.
val cargoVersion: String = run {
    val pkgSection = workspaceRoot.resolve("Cargo.toml").readText()
        .substringAfter("[workspace.package]").substringBefore("\n[")
    Regex("""(?m)^\s*version\s*=\s*"([^"]+)"""").find(pkgSection)?.groupValues?.get(1)
        ?: error("Could not find [workspace.package].version in ${workspaceRoot.resolve("Cargo.toml")}")
}

// Generated outputs land in AGP's conventional source dirs (gitignored). AGP
// packages src/main/jniLibs/<abi>/*.so and compiles src/main/kotlin by default.
val jniLibsOut = file("$projectDir/src/main/jniLibs")
val bindingsOut = file("$projectDir/src/main/kotlin")

val ndkVer = providers.gradleProperty("ndkVersion").getOrElse("30.0.14904198")
val noUndefinedLinkerFlag = "-C link-arg=-Wl,--no-undefined"
val buildIdLinkerFlag = "-C link-arg=-Wl,--build-id=sha1"

android {
    namespace = "com.kss.euid.zk.sdk"
    compileSdk = 36
    // Installed NDK; AGP uses it to strip the bundled .so on release packaging,
    // and we hand it to cargo-ndk below. Must be installed (AGP 9.2's default is
    // 28.2.13676358). Override with `-PndkVersion=<installed-version>` when needed.
    ndkVersion = ndkVer

    defaultConfig {
        minSdk = 24
        // Instrumented tests (src/androidTest) run on an emulator/device and load
        // the bundled ABI .so — no host-arch build needed.
        testInstrumentationRunner = "androidx.test.runner.AndroidJUnitRunner"
    }

    publishing {
        // One AAR variant — we don't ship a debug build of the contract.
        singleVariant("release")
    }
}

// Resolve the SDK/NDK location ourselves (AGP 9 removed android.ndkDirectory).
val androidSdkDir: String = System.getenv("ANDROID_HOME")
    ?: System.getenv("ANDROID_SDK_ROOT")
    ?: file("$projectDir/local.properties").takeIf { it.exists() }
        ?.readLines()
        ?.firstOrNull { it.startsWith("sdk.dir=") }
        ?.substringAfter("=")
        ?.trim()
    ?: "${System.getProperty("user.home")}/Library/Android/sdk"
val ndkHome = "$androidSdkDir/ndk/$ndkVer"

// PATH that still finds the Rust toolchain when Gradle is launched by Android
// Studio (which doesn't inherit the login shell's PATH).
val toolBinDirs = listOf(
    "${System.getProperty("user.home")}/.cargo/bin",
    "/opt/homebrew/bin",
    "/usr/local/bin",
)
val toolPath = (toolBinDirs + (System.getenv("PATH") ?: "")).joinToString(File.pathSeparator)

// Absolute path to `cargo`. Gradle resolves the *executable* name against the
// daemon's PATH (not the environment() we set on the task), and the daemon —
// especially when started by Android Studio — has no ~/.cargo/bin. So launch
// cargo by absolute path; the PATH env above then lets cargo find cargo-ndk etc.
val cargoExe = toolBinDirs.map { "$it/cargo" }.firstOrNull { file(it).exists() } ?: "cargo"

// 1. Cross-compile libeuid_zk_sdk.so for each ABI -> src/main/jniLibs/<abi>/libeuid_zk_sdk.so.
val cargoNdkBuild by tasks.registering(Exec::class) {
    group = "rust"
    description = "Cross-compile libeuid_zk_sdk.so for Android ABIs via cargo-ndk."
    workingDir = workspaceRoot
    environment("PATH", toolPath)
    environment("ANDROID_NDK_HOME", ndkHome)
    // Reject unresolved native symbols at link time. Android otherwise permits them in a
    // shared object and reports the problem only when JNA calls dlopen().
    val linkerFlags = mutableListOf(noUndefinedLinkerFlag)
    // Opt-in via `-PemitBuildId=true` (see the `publish-android-symbols` make target):
    // emit a GNU build-id note into each .so so Perfetto/heapprofd & simpleperf can
    // match the stripped on-device lib to the local unstripped copy in jniLibs for
    // offline symbolization (DWARF itself is already on via [profile.release] debug).
    // Scoped per Android target through CARGO_TARGET_<triple>_RUSTFLAGS so the host
    // build scripts / proc-macros — linked by Apple ld, which rejects --build-id —
    // are left untouched. Set on the forked process here, so it reaches cargo
    // regardless of the Gradle daemon's own environment.
    val emitBuildId = (project.findProperty("emitBuildId") as String?)?.toBoolean() ?: false
    if (emitBuildId) {
        linkerFlags += buildIdLinkerFlag
    }
    inputs.property("emitBuildId", emitBuildId)
    inputs.property("linkerFlags", linkerFlags)
    environment("CARGO_TARGET_AARCH64_LINUX_ANDROID_RUSTFLAGS", linkerFlags.joinToString(" "))
    environment("CARGO_TARGET_X86_64_LINUX_ANDROID_RUSTFLAGS", linkerFlags.joinToString(" "))
    commandLine(
        cargoExe, "ndk",
        "-t", "arm64-v8a", "-t", "x86_64",
        "-o", jniLibsOut.absolutePath,
        "build", "--release", "-p", "sdk",
    )
    inputs.dir(crateDir.resolve("src"))
    inputs.file(crateDir.resolve("Cargo.toml"))
    outputs.dir(jniLibsOut)
    outputs.upToDateWhen { false }
}

// 2. Generate the UniFFI Kotlin bindings from a built .so (proc-macro metadata
//    is embedded in the cdylib, so --library is all uniffi-bindgen needs). Reads
//    the same uniffi.toml the CLI script uses -> identical output.
val generateUniffiBindings by tasks.registering(Exec::class) {
    group = "rust"
    description = "Generate UniFFI Kotlin bindings for the sdk crate."
    dependsOn(cargoNdkBuild)
    workingDir = workspaceRoot
    environment("PATH", toolPath)
    val builtLib = jniLibsOut.resolve("arm64-v8a/libeuid_zk_sdk.so")
    commandLine(
        cargoExe, "run", "-p", "sdk", "--features", "bindgen", "--bin", "uniffi-bindgen", "--",
        "generate",
        "--library", builtLib.absolutePath,
        "--language", "kotlin",
        "--config", uniffiConfig.absolutePath,
        "--out-dir", bindingsOut.absolutePath,
    )
    inputs.file(uniffiConfig)
    inputs.dir(crateDir.resolve("src"))
    inputs.file(crateDir.resolve("Cargo.toml"))
    inputs.file(builtLib)
    outputs.dir(bindingsOut)
}

// Bindings + native libs must exist before Kotlin compiles / AGP merges jniLibs.
tasks.named("preBuild") { dependsOn(generateUniffiBindings) }

dependencies {
    // UniFFI's Kotlin runtime is JNA-based; `api` makes it transitive so
    // consumers don't have to declare it.
    api("net.java.dev.jna:jna:5.19.1@aar")

    // Instrumented tests only.
    androidTestImplementation("androidx.test.ext:junit:1.3.0")
    androidTestImplementation("androidx.test:runner:1.7.0")
}

publishing {
    publications {
        register<MavenPublication>("release") {
            groupId = "com.kss"
            artifactId = "eu-id-zk-sdk"
            version = cargoVersion
            // `release` component isn't available until AGP configures it.
            afterEvaluate { from(components["release"]) }
        }
    }
    // No `repositories {}` block -> `publishToMavenLocal` targets ~/.m2.
}
