plugins {
    id("com.android.application") version "9.2.1"
}

abstract class GeneratedDirectorySync : Sync() {
    @get:OutputDirectory
    abstract val outputDirectory: DirectoryProperty
}

dependencies {
    testImplementation("junit:junit:4.13.2")
}

val workspaceRoot = file("$projectDir/../..")
val jniLibsOut = layout.buildDirectory.dir("generated/jniLibs")
val benchAssetsOut = layout.buildDirectory.dir("generated/benchAssets")
val ndkVersionInstalled = "27.1.12297006"
// Validate each input when Gradle resolves it.
// A `Sync` task skips `doFirst` when its source set is empty.
// That task can remove the staged native libraries and still succeed.
fun requireBenchInput(property: String, path: File, description: String): File {
    require(path.isFile) {
        "$property must point to $description; set -P$property=/absolute/path"
    }
    return path
}
val productSo = providers.gradleProperty("productSo")
    .orElse("$projectDir/prebuilt/sdk-product/arm64-v8a/libeuid_zk_sdk.so")
    .map { path ->
        requireBenchInput(
            "productSo",
            file(path),
            "the fat-LTO product arm64-v8a libeuid_zk_sdk.so",
        )
    }
val productManifest = providers.gradleProperty("productManifest")
    .orElse("$projectDir/prebuilt/sdk-product/build-manifest.json")
    .map { path ->
        requireBenchInput(
            "productManifest",
            file(path),
            "the product native build manifest",
        )
    }
val productPackagedName = "libeuid_zk_sdk.so"
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

    sourceSets.getByName("main").apply {
        jniLibs.directories.clear()
        assets.directories.clear()
    }

    buildTypes {
        release {
            isMinifyEnabled = false
            // Use the standard debug key for this benchmark-only APK.
            // This permits local installation and Test Lab upload.
            signingConfig = signingConfigs.getByName("debug")
        }
    }
}

val stageProductLibrary by tasks.registering(GeneratedDirectorySync::class) {
    group = "rust"
    description = "Stage the product P-256 JNI library into the benchmark APK."
    inputs.file(productSo)
        .withPropertyName("productSo")
        .withPathSensitivity(PathSensitivity.NONE)
    from(productSo) {
        rename { productPackagedName }
    }
    outputDirectory.set(jniLibsOut)
    into(outputDirectory.dir("arm64-v8a"))
}

val stageProductManifest by tasks.registering(GeneratedDirectorySync::class) {
    group = "rust"
    description = "Package the native product build provenance."
    inputs.file(productManifest)
        .withPropertyName("productManifest")
        .withPathSensitivity(PathSensitivity.NONE)
    from(productManifest) {
        rename { "sdk_product_build_manifest.json" }
    }
    outputDirectory.set(benchAssetsOut)
    into(outputDirectory)
}

androidComponents.onVariants { variant ->
    variant.sources.jniLibs?.addGeneratedSourceDirectory(stageProductLibrary) {
        it.outputDirectory
    }
    variant.sources.assets?.addGeneratedSourceDirectory(stageProductManifest) {
        it.outputDirectory
    }
}

tasks.withType<AbstractArchiveTask>().configureEach {
    isPreserveFileTimestamps = false
    isReproducibleFileOrder = true
}
