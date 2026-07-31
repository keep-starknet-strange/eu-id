// Build the Rust library, generate the Kotlin bindings, and package one AAR.

plugins {
    id("com.android.library") version "9.2.1"
    id("maven-publish")
}

val workspaceRoot = file("$projectDir/../../..")
val crateDir = file("$projectDir/..")
val uniffiConfig = file("$projectDir/../uniffi.toml")

// Use the Cargo workspace version for the AAR.
val cargoVersion: String = run {
    val pkgSection = workspaceRoot.resolve("Cargo.toml").readText()
        .substringAfter("[workspace.package]").substringBefore("\n[")
    Regex("""(?m)^\s*version\s*=\s*"([^"]+)"""").find(pkgSection)?.groupValues?.get(1)
        ?: error("Could not find [workspace.package].version in ${workspaceRoot.resolve("Cargo.toml")}")
}

val jniLibsOut = layout.buildDirectory.dir("generated/uniffi/jniLibs").get().asFile
val bindingsOut = layout.buildDirectory.dir("generated/uniffi/kotlin").get().asFile

val ndkVer = providers.gradleProperty("ndkVersion").getOrElse("27.1.12297006")
val noUndefinedLinkerFlag = "-C link-arg=-Wl,--no-undefined"

android {
    namespace = "com.kss.euid.zk.sdk"
    compileSdk = 36
    ndkVersion = ndkVer

    defaultConfig {
        minSdk = 24
    }

    publishing {
        singleVariant("release")
    }
}

androidComponents.onVariants { variant ->
    variant.sources.jniLibs?.addStaticSourceDirectory(jniLibsOut.absolutePath)
    variant.sources.kotlin?.addStaticSourceDirectory(bindingsOut.absolutePath)
}

// Find the Android SDK and NDK.
val androidSdkDir: String = System.getenv("ANDROID_HOME")
    ?: System.getenv("ANDROID_SDK_ROOT")
    ?: file("$projectDir/local.properties").takeIf { it.exists() }
        ?.readLines()
        ?.firstOrNull { it.startsWith("sdk.dir=") }
        ?.substringAfter("=")
        ?.trim()
    ?: "${System.getProperty("user.home")}/Library/Android/sdk"
val ndkHome = "$androidSdkDir/ndk/$ndkVer"

// Add common Rust tool locations for Android Studio.
val toolBinDirs = listOf(
    "${System.getProperty("user.home")}/.cargo/bin",
    "/opt/homebrew/bin",
    "/usr/local/bin",
)
val toolPath = (toolBinDirs + (System.getenv("PATH") ?: "")).joinToString(File.pathSeparator)

// Use an absolute Cargo path when Android Studio does not inherit the shell path.
val cargoExe = toolBinDirs.map { "$it/cargo" }.firstOrNull { file(it).exists() } ?: "cargo"

val cargoNdkBuild by tasks.registering(Exec::class) {
    group = "rust"
    description = "Cross-compile libeuid_zk_sdk.so for Android ABIs via cargo-ndk."
    workingDir = workspaceRoot
    environment("PATH", toolPath)
    environment("ANDROID_NDK_HOME", ndkHome)
    inputs.property("linkerFlag", noUndefinedLinkerFlag)
    environment("CARGO_TARGET_AARCH64_LINUX_ANDROID_RUSTFLAGS", noUndefinedLinkerFlag)
    environment("CARGO_TARGET_X86_64_LINUX_ANDROID_RUSTFLAGS", noUndefinedLinkerFlag)
    doFirst { delete(jniLibsOut) }
    commandLine(
        cargoExe, "ndk",
        "-t", "arm64-v8a", "-t", "x86_64",
        "-o", jniLibsOut.absolutePath,
        "build", "--locked", "--release", "-p", "sdk",
    )
    inputs.dir(crateDir.resolve("src"))
    inputs.file(crateDir.resolve("Cargo.toml"))
    outputs.dir(jniLibsOut)
    outputs.upToDateWhen { false }
}

val generateUniffiBindings by tasks.registering(Exec::class) {
    group = "rust"
    description = "Generate UniFFI Kotlin bindings for the sdk crate."
    dependsOn(cargoNdkBuild)
    workingDir = workspaceRoot
    environment("PATH", toolPath)
    val builtLib = jniLibsOut.resolve("arm64-v8a/libeuid_zk_sdk.so")
    doFirst { delete(bindingsOut) }
    commandLine(
        cargoExe, "run", "--locked", "--release", "-p", "sdk",
        "--features", "bindgen", "--bin", "uniffi-bindgen", "--",
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

tasks.named("preBuild") { dependsOn(generateUniffiBindings) }

dependencies {
    // Publish JNA as an API dependency.
    api("net.java.dev.jna:jna:5.19.1@aar")
}

publishing {
    publications {
        register<MavenPublication>("release") {
            groupId = "com.kss"
            artifactId = "eu-id-zk-sdk"
            version = cargoVersion
            afterEvaluate { from(components["release"]) }
        }
    }
}
