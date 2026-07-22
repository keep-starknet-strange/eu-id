import java.io.File

plugins {
    id("com.android.application") version "9.2.1"
}

val workspaceRoot = file("$projectDir/../..")
val jniLibsOut = file("$projectDir/src/main/jniLibs")
val ndkVersionInstalled = "27.1.12297006"

fun gitValue(vararg args: String): String = providers.exec {
    workingDir = workspaceRoot
    commandLine("git", *args)
}.standardOutput.asText.get().trim()

fun buildConfigString(value: String): String =
    "\"${value.replace("\\", "\\\\").replace("\"", "\\\"")}\""

val gitCommit = gitValue("rev-parse", "HEAD")
val gitRevision = gitCommit + if (gitValue("status", "--porcelain").isEmpty()) "" else "-dirty"
val stwoRevision = Regex(
    """(?m)^stwo\s*=\s*\{[^\n]*\brev\s*=\s*"([0-9a-f]+)"""",
).find(workspaceRoot.resolve("Cargo.toml").readText())?.groupValues?.get(1)
    ?: error("Could not find workspace stwo revision")

android {
    namespace = "eu.euid.bench"
    compileSdk = 36
    ndkVersion = ndkVersionInstalled

    defaultConfig {
        applicationId = "eu.euid.bench"
        minSdk = 26
        targetSdk = 36
        versionCode = 1
        versionName = "1.0"

        ndk {
            abiFilters += "arm64-v8a"
        }

        buildConfigField("String", "BENCH_BRANCH", buildConfigString(gitValue("rev-parse", "--abbrev-ref", "HEAD")))
        buildConfigField("String", "BENCH_GIT", buildConfigString(gitRevision))
        buildConfigField("String", "STWO_REV", buildConfigString(stwoRevision))
    }

    buildFeatures {
        buildConfig = true
    }

    buildTypes {
        release {
            isMinifyEnabled = false
            // Benchmark-only APK: sign the optimized build with the standard
            // debug key so it can be installed locally and uploaded to Test Lab.
            signingConfig = signingConfigs.getByName("debug")
        }
    }
}

val androidSdkDir = System.getenv("ANDROID_HOME")
    ?: System.getenv("ANDROID_SDK_ROOT")
    ?: file("$projectDir/local.properties").takeIf { it.exists() }
        ?.readLines()
        ?.firstOrNull { it.startsWith("sdk.dir=") }
        ?.substringAfter("=")
        ?.trim()
    ?: "${System.getProperty("user.home")}/Library/Android/sdk"
val ndkHome = "$androidSdkDir/ndk/$ndkVersionInstalled"
val toolBinDirs = listOf(
    "${System.getProperty("user.home")}/.cargo/bin",
    "/opt/homebrew/bin",
    "/usr/local/bin",
)
val toolPath = (toolBinDirs + (System.getenv("PATH") ?: "")).joinToString(File.pathSeparator)
val cargoExe = toolBinDirs.map { "$it/cargo" }.firstOrNull { file(it).exists() } ?: "cargo"

val cargoNdkBuild by tasks.registering(Exec::class) {
    group = "rust"
    description = "Build the arm64 eu-id benchmark JNI library."
    workingDir = workspaceRoot
    environment("PATH", toolPath)
    environment("ANDROID_NDK_HOME", ndkHome)
    commandLine(
        cargoExe,
        "ndk",
        "-t",
        "arm64-v8a",
        "-o",
        jniLibsOut.absolutePath,
        "build",
        "--release",
        "--locked",
        "-p",
        "eu-id-ffi",
        "--features",
        "jni",
    )
    inputs.files(
        workspaceRoot.resolve("Cargo.toml"),
        workspaceRoot.resolve("Cargo.lock"),
        workspaceRoot.resolve("crates/eu-id-ffi/Cargo.toml"),
    )
    inputs.dir(workspaceRoot.resolve("crates/eu-id-ffi/src"))
    outputs.dir(jniLibsOut)
    outputs.upToDateWhen { false }
}

tasks.named("preBuild") {
    dependsOn(cargoNdkBuild)
}
