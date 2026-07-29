import groovy.json.JsonSlurper
import java.security.MessageDigest

plugins {
    id("com.android.application") version "9.2.1"
}

dependencies {
    testImplementation("junit:junit:4.13.2")
}

val workspaceRoot = file("$projectDir/../..")
val jniLibsOut = layout.buildDirectory.dir("generated/jniLibs")
val benchAssetsOut = layout.buildDirectory.dir("generated/benchAssets")
val ndkVersionInstalled = "27.1.12297006"
val benchmarkProfile = "full_pq_mdoc_mldsa65_ts13_revocation_paired"
val benchmarkEntrypoint = "fullPq"
fun requireBenchInput(property: String, path: File, description: String): File {
    require(path.isFile) {
        "$property must point to $description; set -P$property=/absolute/path"
    }
    return path
}
fun sha256(file: File): String = MessageDigest.getInstance("SHA-256")
    .digest(file.readBytes())
    .joinToString("") { "%02x".format(it) }
fun requireBenchManifest(
    property: String,
    path: File,
    library: File,
    slot: String,
    variant: String,
): File {
    requireBenchInput(property, path, "the $variant ML-DSA native build manifest")
    val manifest = JsonSlurper().parse(path) as? Map<*, *>
        ?: error("$property must contain a JSON object")
    fun field(name: String): String = manifest[name] as? String
        ?: error("$property is missing string field '$name'")
    require(manifest["schema"] == 1) { "$property has an unsupported schema" }
    require(field("library_slot") == slot) { "$property belongs to the wrong library slot" }
    require(field("benchmark_variant") == variant) { "$property belongs to the wrong variant" }
    require(field("benchmark_entrypoint") == benchmarkEntrypoint) {
        "$property does not describe the $benchmarkEntrypoint benchmark"
    }
    require(field("benchmark_profile") == benchmarkProfile) {
        "$property does not describe the current full-PQ profile"
    }
    require(field("source_ref") == field("git_commit")) {
        "$property does not bind its source ref to its commit"
    }
    require(field("git_commit").matches(Regex("[0-9a-f]{40}"))) {
        "$property has an invalid source commit"
    }
    require(manifest["git_dirty"] == false) { "$property must come from a clean source tree" }
    require(field("source_sha256_no_md").matches(Regex("[0-9a-f]{64}"))) {
        "$property has an invalid source hash"
    }
    require(field("build_id").matches(Regex("[0-9a-f]{64}"))) {
        "$property has an invalid build id"
    }
    require(field("rustc").isNotBlank()) { "$property is missing the Rust compiler version" }
    require(field("ndk_revision") == ndkVersionInstalled) { "$property has the wrong Android NDK" }
    require(field("target_abi") == "arm64-v8a") { "$property has the wrong ABI" }
    require(field("cargo_profile") == "bench") { "$property was not built with Cargo's bench profile" }
    require(field("lto") == "fat") { "$property was not built with fat LTO" }
    require(manifest["codegen_units"] == 1) { "$property must use one codegen unit" }
    require((manifest["features"] as? List<*>) == listOf("jni")) {
        "$property must record exactly the JNI feature set"
    }
    require(field("unstripped_library_sha256") == sha256(library)) {
        "$property does not match the supplied native library"
    }
    return path
}
val mldsaReferenceSo = providers.gradleProperty("mldsaReferenceSo")
    .orElse("$projectDir/prebuilt/mldsa-reference/arm64-v8a/libeu_id_ffi.so")
    .map { path -> requireBenchInput("mldsaReferenceSo", file(path), "the fat-LTO reference arm64-v8a libeu_id_ffi.so") }
val mldsaCandidateSo = providers.gradleProperty("mldsaCandidateSo")
    .orElse("$projectDir/prebuilt/mldsa-candidate/arm64-v8a/libeu_id_ffi.so")
    .map { path -> requireBenchInput("mldsaCandidateSo", file(path), "the fat-LTO candidate arm64-v8a libeu_id_ffi.so") }
val mldsaReferenceManifest = providers.gradleProperty("mldsaReferenceManifest")
    .orElse("$projectDir/prebuilt/mldsa-reference/build-manifest.json")
    .map { path -> requireBenchManifest("mldsaReferenceManifest", file(path), mldsaReferenceSo.get(), "mldsa-reference", "reference") }
val mldsaCandidateManifest = providers.gradleProperty("mldsaCandidateManifest")
    .orElse("$projectDir/prebuilt/mldsa-candidate/build-manifest.json")
    .map { path -> requireBenchManifest("mldsaCandidateManifest", file(path), mldsaCandidateSo.get(), "mldsa-candidate", "candidate") }
val mldsaReferencePackagedName = "libeu_id_ffi_mldsa_reference.so"
val mldsaCandidatePackagedName = "libeu_id_ffi_mldsa_candidate.so"

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

        buildConfigField(
            "String",
            "BENCH_BRANCH",
            buildConfigString(gitValue("rev-parse", "--abbrev-ref", "HEAD")),
        )
        buildConfigField("String", "BENCH_GIT", buildConfigString(gitRevision))
        buildConfigField("String", "STWO_REV", buildConfigString(stwoRevision))
    }

    buildFeatures {
        buildConfig = true
    }

    packaging {
        jniLibs.keepDebugSymbols += "**/*.so"
    }

    sourceSets["main"].jniLibs.setSrcDirs(listOf(jniLibsOut))
    sourceSets["main"].assets.srcDir(benchAssetsOut.get().asFile)

    buildTypes {
        release {
            isMinifyEnabled = false
            signingConfig = signingConfigs.getByName("debug")
        }
    }
}

val stageMldsaBenchLibraries by tasks.registering(Sync::class) {
    group = "rust"
    description = "Stage the prebuilt ML-DSA reference and candidate JNI libraries into one APK."
    inputs.file(mldsaReferenceSo)
        .withPropertyName("mldsaReferenceSo")
        .withPathSensitivity(PathSensitivity.NONE)
    inputs.file(mldsaCandidateSo)
        .withPropertyName("mldsaCandidateSo")
        .withPathSensitivity(PathSensitivity.NONE)
    from(mldsaReferenceSo) {
        rename { mldsaReferencePackagedName }
    }
    from(mldsaCandidateSo) {
        rename { mldsaCandidatePackagedName }
    }
    into(jniLibsOut.map { it.dir("arm64-v8a") })
}

val stageMldsaBenchManifests by tasks.registering(Sync::class) {
    group = "rust"
    description = "Package verified native build provenance for both ML-DSA libraries."
    inputs.file(mldsaReferenceManifest)
        .withPropertyName("mldsaReferenceManifest")
        .withPathSensitivity(PathSensitivity.NONE)
    inputs.file(mldsaCandidateManifest)
        .withPropertyName("mldsaCandidateManifest")
        .withPathSensitivity(PathSensitivity.NONE)
    from(mldsaReferenceManifest) {
        rename { "mldsa_reference_build_manifest.json" }
    }
    from(mldsaCandidateManifest) {
        rename { "mldsa_candidate_build_manifest.json" }
    }
    into(benchAssetsOut)
}

tasks.named("preBuild") {
    dependsOn(stageMldsaBenchLibraries, stageMldsaBenchManifests)
}
