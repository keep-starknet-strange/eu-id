// Packages the `sdk` Rust crate into a plug-and-play **desktop/JVM** fat jar so the
// wallet/verifier can run native unit tests on a host JVM (no emulator/device).
//
//   - buildNative_<platform>  builds libeuid_zk_sdk for each host target:
//       * apple-darwin  via plain `cargo build`  (native + cross x86_64 on Apple Silicon)
//       * linux / windows via `cargo zigbuild`   (needs `zig` + cargo-zigbuild)
//     and lays each under JNA's classpath layout `build/nativeLibs/<jna-prefix>/`.
//   - generateUniffiBindings  emits the identical UniFFI Kotlin bindings (from a built
//     cdylib's embedded metadata) — same contract as the AAR, no divergence.
//   - the jar bundles bindings (classes) + all natives (resources); JNA extracts the
//     matching platform's lib at runtime.
//   - maven-publish ships `com.kss:eu-id-zk-sdk-jvm:0.1.0` to ~/.m2.
//
// Consumer (wallet :zkp-logic):  testImplementation("com.kss:eu-id-zk-sdk-jvm:0.1.0")

plugins {
    kotlin("jvm") version "2.0.21"
    `maven-publish`
}

group = "com.kss"

repositories { mavenCentral() }

// Layout, relative to this project dir (crates/sdk/jvm):
//   ../        -> crates/sdk     (uniffi.toml)
//   ../../..   -> Cargo workspace root (for `cargo ... -p sdk`)
val workspaceRoot = file("$projectDir/../../..")
val crateDir = file("$projectDir/..")
val uniffiConfig = file("$projectDir/../uniffi.toml")

// Single source of truth for the published version: the Cargo workspace. Crates
// set `version.workspace = true`, so the literal lives in the root Cargo.toml
// under [workspace.package] — the same value Rust sees as CARGO_PKG_VERSION.
// Parse it here so the jar version can never drift from the crate; bump it once
// in the Cargo manifest.
val cargoVersion: String = run {
    val pkgSection = workspaceRoot.resolve("Cargo.toml").readText()
        .substringAfter("[workspace.package]").substringBefore("\n[")
    Regex("""(?m)^\s*version\s*=\s*"([^"]+)"""").find(pkgSection)?.groupValues?.get(1)
        ?: error("Could not find [workspace.package].version in ${workspaceRoot.resolve("Cargo.toml")}")
}
version = cargoVersion

val generatedKotlinDir = layout.buildDirectory.dir("generated/uniffi").get().asFile
val nativeLibsDir = layout.buildDirectory.dir("nativeLibs").get().asFile

// PATH that finds cargo / cargo-zigbuild / zig even when Gradle isn't launched
// from a login shell. cargo is invoked by absolute path (Gradle resolves the
// executable against the daemon PATH, not the task environment()).
val toolBinDirs = listOf(
    "${System.getProperty("user.home")}/.cargo/bin",
    "/opt/homebrew/bin",
    "/usr/local/bin",
)
val toolPath = (toolBinDirs + (System.getenv("PATH") ?: "")).joinToString(File.pathSeparator)
val cargoExe = toolBinDirs.map { "$it/cargo" }.firstOrNull { file(it).exists() } ?: "cargo"

// Rust target -> JNA classpath prefix + output lib filename. Whether zig is needed
// is decided per-host by [needsZig] (you only need it to cross-compile), not baked
// into the target.
data class NativeTarget(
    val rustTarget: String,
    val jnaPrefix: String,
    val libFile: String,
) {
    val targetOs: String
        get() = when {
            rustTarget.contains("apple-darwin") -> "macos"
            rustTarget.contains("windows") -> "windows"
            else -> "linux"
        }
    val targetArch: String
        get() = if (rustTarget.startsWith("aarch64")) "arm64" else "x86_64"

    /**
     * zig is needed only to *cross*-compile: to a different OS, or (on Linux/Windows) a
     * different arch. The host toolchain builds its own OS directly — and on macOS, clang
     * cross-builds arm64<->x86_64 natively, so neither darwin arch needs zig there.
     */
    val needsZig: Boolean
        get() = when {
            targetOs != HOST_OS -> true
            HOST_OS == "macos" -> false
            else -> targetArch != HOST_ARCH
        }
}

// Detected once. NOTE: apple-darwin targets can only be produced on a macOS host.
val HOST_OS: String = System.getProperty("os.name").lowercase().let {
    when {
        it.contains("mac") || it.contains("darwin") -> "macos"
        it.contains("win") -> "windows"
        else -> "linux"
    }
}
val HOST_ARCH: String =
    if (System.getProperty("os.arch").lowercase().let { it.contains("aarch64") || it.contains("arm64") }) "arm64"
    else "x86_64"

val allNativeTargets = listOf(
    NativeTarget("aarch64-apple-darwin", "darwin-aarch64", "libeuid_zk_sdk.dylib"),
    NativeTarget("x86_64-apple-darwin", "darwin-x86-64", "libeuid_zk_sdk.dylib"),
    NativeTarget("x86_64-unknown-linux-gnu", "linux-x86-64", "libeuid_zk_sdk.so"),
    NativeTarget("aarch64-unknown-linux-gnu", "linux-aarch64", "libeuid_zk_sdk.so"),
    NativeTarget("x86_64-pc-windows-gnu", "win32-x86-64", "euid_zk_sdk.dll"),
)

// Opt-in (`-PhostOnlyNative`): build only the host desktop native, skipping the
// Linux/Windows cross-builds. For local host unit testing where a full cross-platform
// fat jar isn't needed (and the zig Windows cross-build may be unavailable). Default off
// so published/CI jars stay cross-platform.
val nativeTargets = if (providers.gradleProperty("hostOnlyNative").isPresent) {
    allNativeTargets.filter { it.targetOs == HOST_OS && it.targetArch == HOST_ARCH }
} else {
    allNativeTargets
}

val buildNativeTasks = nativeTargets.map { t ->
    tasks.register<Exec>("buildNative_${t.jnaPrefix.replace('-', '_')}") {
        group = "rust"
        description = "Build ${t.rustTarget} -> ${t.jnaPrefix}/${t.libFile}"
        workingDir = workspaceRoot
        environment("PATH", toolPath)
        val sub = if (t.needsZig) "zigbuild" else "build"
        commandLine(cargoExe, sub, "--release", "-p", "sdk", "--target", t.rustTarget)

        inputs.dir(crateDir.resolve("src"))
        inputs.file(crateDir.resolve("Cargo.toml"))
        val builtLib = workspaceRoot.resolve("target/${t.rustTarget}/release/${t.libFile}")
        val destDir = File(nativeLibsDir, t.jnaPrefix)
        outputs.file(File(destDir, t.libFile))
        doLast { copy { from(builtLib); into(destDir) } }
        outputs.upToDateWhen { false }
    }
}

// The host cdylib (darwin-aarch64) carries the UniFFI metadata bindgen introspects.
val hostNativeTask = buildNativeTasks.first()
val hostLib = workspaceRoot.resolve("target/aarch64-apple-darwin/release/libeuid_zk_sdk.dylib")

val generateUniffiBindings by tasks.registering(Exec::class) {
    group = "rust"
    description = "Generate UniFFI Kotlin bindings for the sdk crate."
    dependsOn(hostNativeTask)
    workingDir = workspaceRoot
    environment("PATH", toolPath)
    commandLine(
        cargoExe, "run", "-p", "sdk", "--features", "bindgen", "--bin", "uniffi-bindgen", "--",
        "generate",
        "--library", hostLib.absolutePath,
        "--language", "kotlin",
        "--config", uniffiConfig.absolutePath,
        "--out-dir", generatedKotlinDir.absolutePath,
    )
    inputs.file(uniffiConfig)
    inputs.dir(crateDir.resolve("src"))
    outputs.dir(generatedKotlinDir)
}

// Generated bindings are .kt; the Kotlin compiler picks up `java` source dirs too.
sourceSets["main"].java.srcDir(generatedKotlinDir)
sourceSets["main"].resources.srcDir(nativeLibsDir)

tasks.named("compileKotlin") { dependsOn(generateUniffiBindings) }
tasks.named("processResources") { dependsOn(buildNativeTasks) }

dependencies {
    // UniFFI's Kotlin runtime is JNA-based; `api` so consumers get it transitively.
    api("net.java.dev.jna:jna:5.19.1")
    implementation(kotlin("stdlib"))
}

publishing {
    publications {
        register<MavenPublication>("jvm") {
            groupId = "com.kss"
            artifactId = "eu-id-zk-sdk-jvm"
            version = cargoVersion
            from(components["java"])
        }
    }
    // No `repositories {}` -> publishToMavenLocal targets ~/.m2.
}
