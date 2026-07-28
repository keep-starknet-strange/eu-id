plugins {
    id("com.android.application") version "9.2.1"
    id("com.google.gms.google-services") version "4.5.0"
}

dependencies {
    implementation(platform("com.google.firebase:firebase-bom:34.16.0"))
    testImplementation("junit:junit:4.13.2")
}

val workspaceRoot = file("$projectDir/../..")
val jniLibsOut = layout.buildDirectory.dir("generated/jniLibs")
val benchAssetsOut = layout.buildDirectory.dir("generated/benchAssets")
val ndkVersionInstalled = "27.1.12297006"
// Validate at resolution time, NOT in the Sync task's doFirst: a Sync task
// whose source files are missing runs with an empty source set, skips doFirst
// checks, and deletes everything already staged in the destination — a green
// build that ships an APK with no native libraries.
fun requireBenchInput(property: String, path: File, description: String): File {
    require(path.isFile) {
        "$property must point to $description; set -P$property=/absolute/path"
    }
    return path
}
val p256Range16So = providers.gradleProperty("p256Range16So")
    .orElse("$projectDir/prebuilt/p256-range16/arm64-v8a/libeuid_zk_sdk.so")
    .map { path ->
        requireBenchInput(
            "p256Range16So",
            file(path),
            "the fat-LTO revocation-enabled arm64-v8a libeuid_zk_sdk.so",
        )
    }
val p256Range8So = providers.gradleProperty("p256Range8So")
    .orElse("$projectDir/prebuilt/p256-range8/arm64-v8a/libeuid_zk_sdk.so")
    .map { path ->
        requireBenchInput(
            "p256Range8So",
            file(path),
            "the fat-LTO revocation-disabled arm64-v8a libeuid_zk_sdk.so",
        )
    }
val p256Range16Manifest = providers.gradleProperty("p256Range16Manifest")
    .orElse("$projectDir/prebuilt/p256-range16/build-manifest.json")
    .map { path ->
        requireBenchInput(
            "p256Range16Manifest",
            file(path),
            "the revocation-enabled native build manifest",
        )
    }
val p256Range8Manifest = providers.gradleProperty("p256Range8Manifest")
    .orElse("$projectDir/prebuilt/p256-range8/build-manifest.json")
    .map { path ->
        requireBenchInput(
            "p256Range8Manifest",
            file(path),
            "the revocation-disabled native build manifest",
        )
    }
val p256Range16PackagedName = "libeuid_zk_sdk_p256_range16.so"
val p256Range8PackagedName = "libeuid_zk_sdk_p256_range8.so"
val p256BigCores = providers.gradleProperty("p256BigCores")
    .orElse("true")
    .map { value ->
        require(value == "true" || value == "false") {
            "p256BigCores must be true or false"
        }
        value.toBoolean()
    }
    .get()

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
        buildConfigField("boolean", "P256_BIG_CORES", p256BigCores.toString())
    }

    buildFeatures {
        buildConfig = true
    }

    sourceSets["main"].jniLibs.setSrcDirs(listOf(jniLibsOut))
    sourceSets["main"].assets.srcDir(benchAssetsOut.get().asFile)

    buildTypes {
        release {
            isMinifyEnabled = false
            // Benchmark-only APK: sign the optimized build with the standard
            // debug key so it can be installed locally and uploaded to Test Lab.
            signingConfig = signingConfigs.getByName("debug")
        }
    }
}

val stageP256BenchLibraries by tasks.registering(Sync::class) {
    group = "rust"
    description = "Stage the prebuilt P-256 Range16 and Range8 JNI libraries into one APK."
    inputs.file(p256Range16So)
        .withPropertyName("p256Range16So")
        .withPathSensitivity(PathSensitivity.NONE)
    inputs.file(p256Range8So)
        .withPropertyName("p256Range8So")
        .withPathSensitivity(PathSensitivity.NONE)
    from(p256Range16So) {
        rename { p256Range16PackagedName }
    }
    from(p256Range8So) {
        rename { p256Range8PackagedName }
    }
    into(jniLibsOut.map { it.dir("arm64-v8a") })
}

val stageP256BenchManifests by tasks.registering(Sync::class) {
    group = "rust"
    description = "Package the exact native build provenance for both benchmark libraries."
    inputs.file(p256Range16Manifest)
        .withPropertyName("p256Range16Manifest")
        .withPathSensitivity(PathSensitivity.NONE)
    inputs.file(p256Range8Manifest)
        .withPropertyName("p256Range8Manifest")
        .withPathSensitivity(PathSensitivity.NONE)
    from(p256Range16Manifest) {
        rename { "p256_range16_build_manifest.json" }
    }
    from(p256Range8Manifest) {
        rename { "p256_range8_build_manifest.json" }
    }
    into(benchAssetsOut)
}

tasks.named("preBuild") {
    dependsOn(stageP256BenchLibraries, stageP256BenchManifests)
}
