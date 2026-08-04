// Build the `sdk` Rust crate as an Android AAR.
// `cargoNdkBuild` builds the final `libeuid_zk_sdk.so` for each ABI.
// `generateUniffiBindings` creates the Kotlin bindings.
// Android Gradle Plugin packages the native libraries and bindings.
// Maven Publish sends the AAR to the local Maven repository.
//
// Add this dependency to an Android consumer:
//   repositories { mavenLocal() }
//   implementation("com.kss:eu-id-zk-sdk:0.1.0")
//
// AGP 9.2 requires Gradle 9.4.1 or later and JDK 17 or later.
// AGP supplies Kotlin support. Do not add the standalone Kotlin Android plugin.

plugins {
    id("com.android.library") version "9.2.1"
    id("maven-publish")
}

abstract class GeneratedDirectoryExec : Exec() {
    @get:OutputDirectory
    abstract val outputDirectory: DirectoryProperty
}

// Resolve the SDK crate and the workspace from this project directory.
val workspaceRoot = file("$projectDir/../../..")
val uniffiConfig = file("$projectDir/../uniffi.toml")
val reproducibleBuild = workspaceRoot.resolve("scripts/reproducible-build.sh")
val allowDirtyBuild = providers.gradleProperty("allowDirtyBuild")
    .map(String::toBoolean)
    .getOrElse(false)

// Read the published version from `[workspace.package]`.
// This value keeps the AAR version equal to the Rust crate version.
val cargoVersion: String = run {
    val pkgSection = workspaceRoot.resolve("Cargo.toml").readText()
        .substringAfter("[workspace.package]").substringBefore("\n[")
    Regex("""(?m)^\s*version\s*=\s*"([^"]+)"""").find(pkgSection)?.groupValues?.get(1)
        ?: error("Could not find [workspace.package].version in ${workspaceRoot.resolve("Cargo.toml")}")
}

// Keep generated files out of the checked-in source tree.
val jniLibsOut = layout.buildDirectory.dir("generated/jniLibs").get().asFile
val bindingsOut = layout.buildDirectory.dir("generated/uniffi").get().asFile
val legacyGeneratedDirs = listOf(
    file("$projectDir/src/main/jniLibs"),
    file("$projectDir/src/main/kotlin"),
)

val validateNoLegacyGeneratedSources by tasks.registering {
    doLast {
        val present = legacyGeneratedDirs.filter(File::exists)
        require(present.isEmpty()) {
            "remove legacy generated source paths before packaging: " +
                present.joinToString { it.relativeTo(projectDir).path }
        }
    }
}

val ndkVer = "27.1.12297006"
val cargoNdkVer = "4.1.2"
val noUndefinedLinkerFlag = "-C link-arg=-Wl,--no-undefined"
val buildIdLinkerFlag = "-C link-arg=-Wl,--build-id=sha1"

android {
    namespace = "com.kss.euid.zk.sdk"
    compileSdk = 36
    // AGP and cargo-ndk use this pinned NDK version.
    ndkVersion = ndkVer

    defaultConfig {
        minSdk = 24
        // Instrumented tests load the bundled library on an Android target.
        testInstrumentationRunner = "androidx.test.runner.AndroidJUnitRunner"
    }

    publishing {
        // Publish only the release AAR.
        singleVariant("release")
    }
}

// Find the Android SDK because AGP 9 removed `android.ndkDirectory`.
val androidSdkDir: String = System.getenv("ANDROID_HOME")
    ?: System.getenv("ANDROID_SDK_ROOT")
    ?: file("$projectDir/local.properties").takeIf { it.exists() }
        ?.readLines()
        ?.firstOrNull { it.startsWith("sdk.dir=") }
        ?.substringAfter("=")
        ?.trim()
    ?: "${System.getProperty("user.home")}/Library/Android/sdk"
val ndkHome = "$androidSdkDir/ndk/$ndkVer"

// Add common tool directories for Android Studio Gradle processes.
val toolBinDirs = listOf(
    "${System.getProperty("user.home")}/.cargo/bin",
    "/opt/homebrew/bin",
    "/usr/local/bin",
)
val toolPath = (toolBinDirs + (System.getenv("PATH") ?: "")).joinToString(File.pathSeparator)

// Use an absolute Cargo path when one is available.
// The Gradle daemon can have a different `PATH` from the task.
val cargoExe = toolBinDirs.map { "$it/cargo" }.firstOrNull { file(it).exists() } ?: "cargo"
val installedCargoNdkVersion = providers.exec {
    workingDir = workspaceRoot
    environment("PATH", toolPath)
    commandLine(cargoExe, "ndk", "--version")
}.standardOutput.asText
val rustWorkspaceInputs = fileTree(workspaceRoot) {
    include(
        "Cargo.toml",
        "Cargo.lock",
        "rust-toolchain.toml",
        ".cargo/**",
        "artifacts/**",
        "scripts/reproducible-build.sh",
        "crates/*/Cargo.toml",
        "crates/*/build.rs",
        "crates/*/src/**",
        "crates/*/artifacts/**",
        "crates/*/examples/**",
        "crates/*/tests/**",
        "crates/*/benches/**",
    )
}

// Build `libeuid_zk_sdk.so` for each Android ABI.
val cargoNdkBuild by tasks.registering(GeneratedDirectoryExec::class) {
    group = "rust"
    description = "Cross-compile libeuid_zk_sdk.so for Android ABIs via cargo-ndk."
    dependsOn(validateNoLegacyGeneratedSources)
    workingDir = workspaceRoot
    environment("PATH", toolPath)
    environment("ANDROID_NDK_HOME", ndkHome)
    // Reject unresolved symbols and derive the GNU build ID from the ELF content.
    val linkerFlags = listOf(noUndefinedLinkerFlag, buildIdLinkerFlag)
    inputs.property("linkerFlags", linkerFlags)
    inputs.property("ndkVersion", ndkVer)
    inputs.property("cargoNdkVersion", cargoNdkVer)
    inputs.property("allowDirtyBuild", allowDirtyBuild)
    environment("CARGO_TARGET_AARCH64_LINUX_ANDROID_RUSTFLAGS", linkerFlags.joinToString(" "))
    environment("CARGO_TARGET_X86_64_LINUX_ANDROID_RUSTFLAGS", linkerFlags.joinToString(" "))
    val dirtyArgument = if (allowDirtyBuild) listOf("--allow-dirty") else emptyList()
    commandLine(
        listOf("bash", reproducibleBuild.absolutePath) + dirtyArgument + listOf(
        cargoExe, "ndk",
        "-t", "arm64-v8a", "-t", "x86_64",
        "-o", jniLibsOut.absolutePath,
        "rustc", "--locked", "--offline", "--release", "-p", "sdk", "--lib",
        "--crate-type", "cdylib",
        ),
    )
    inputs.files(rustWorkspaceInputs).withPathSensitivity(PathSensitivity.RELATIVE)
    outputDirectory.set(jniLibsOut)
    doFirst {
        val actual = installedCargoNdkVersion.get().trim()
        require(actual == "cargo-ndk $cargoNdkVer") {
            "cargo-ndk $cargoNdkVer is required, got ${actual.ifEmpty { "unknown" }}"
        }
        project.delete(outputDirectory)
    }
}

// Create Kotlin bindings from the metadata in the Android library.
val generateUniffiBindings by tasks.registering(GeneratedDirectoryExec::class) {
    group = "rust"
    description = "Generate UniFFI Kotlin bindings for the sdk crate."
    dependsOn(cargoNdkBuild)
    workingDir = workspaceRoot
    environment("PATH", toolPath)
    val builtLib = jniLibsOut.resolve("arm64-v8a/libeuid_zk_sdk.so")
    val dirtyArgument = if (allowDirtyBuild) listOf("--allow-dirty") else emptyList()
    commandLine(
        listOf("bash", reproducibleBuild.absolutePath) + dirtyArgument + listOf(
        cargoExe, "run", "--locked", "--offline", "-p", "sdk", "--features", "bindgen", "--bin", "uniffi-bindgen", "--",
        "generate",
        "--library", builtLib.absolutePath,
        "--language", "kotlin",
        "--config", uniffiConfig.absolutePath,
        "--out-dir", bindingsOut.absolutePath,
        ),
    )
    inputs.property("allowDirtyBuild", allowDirtyBuild)
    inputs.files(rustWorkspaceInputs).withPathSensitivity(PathSensitivity.RELATIVE)
    inputs.file(uniffiConfig).withPathSensitivity(PathSensitivity.RELATIVE)
    inputs.file(builtLib).withPathSensitivity(PathSensitivity.NONE)
    outputDirectory.set(bindingsOut)
    doFirst { project.delete(outputDirectory) }
}

androidComponents.onVariants { variant ->
    variant.sources.jniLibs?.addGeneratedSourceDirectory(cargoNdkBuild) {
        it.outputDirectory
    }
    variant.sources.kotlin?.addGeneratedSourceDirectory(generateUniffiBindings) {
        it.outputDirectory
    }
}

dependencies {
    // Export the JNA-based UniFFI runtime to consumers.
    api("net.java.dev.jna:jna:5.19.1@aar")

    // Use these dependencies only in instrumented tests.
    androidTestImplementation("androidx.test.ext:junit:1.3.0")
    androidTestImplementation("androidx.test:runner:1.7.0")
}

tasks.withType<AbstractArchiveTask>().configureEach {
    isPreserveFileTimestamps = false
    isReproducibleFileOrder = true
}

publishing {
    publications {
        register<MavenPublication>("release") {
            groupId = "com.kss"
            artifactId = "eu-id-zk-sdk"
            version = cargoVersion
            // Wait until AGP creates the `release` component.
            afterEvaluate { from(components["release"]) }
        }
    }
    // `publishToMavenLocal` writes to the local Maven repository.
}
