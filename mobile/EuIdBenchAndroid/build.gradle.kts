plugins {
    id("com.android.application") version "9.2.1"
}

dependencies {
    testImplementation("junit:junit:4.13.2")
}

val workspaceRoot = file("$projectDir/../..")
val jniLibsOut = layout.buildDirectory.dir("generated/jniLibs")
val ndkVersionInstalled = "27.1.12297006"
val mldsaBaselineSo = providers.gradleProperty("mldsaBaselineSo")
    .map { path -> file(path) }
    .orElse(file("$projectDir/prebuilt/mldsa-baseline/arm64-v8a/libeu_id_ffi.so"))
val mldsaPackedSo = providers.gradleProperty("mldsaPackedSo")
    .map { path -> file(path) }
    .orElse(file("$projectDir/prebuilt/mldsa-packed/arm64-v8a/libeu_id_ffi.so"))
val mldsaBaselinePackagedName = "libeu_id_ffi_mldsa_baseline.so"
val mldsaPackedPackagedName = "libeu_id_ffi_mldsa_packed.so"

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

    sourceSets["main"].jniLibs.setSrcDirs(listOf(jniLibsOut))

    buildTypes {
        release {
            isMinifyEnabled = false
            signingConfig = signingConfigs.getByName("debug")
        }
    }
}

val stageMldsaBenchLibraries by tasks.registering(Sync::class) {
    group = "rust"
    description = "Stage the prebuilt ML-DSA baseline and packed JNI libraries into one APK."
    inputs.file(mldsaBaselineSo)
        .withPropertyName("mldsaBaselineSo")
        .withPathSensitivity(PathSensitivity.NONE)
    inputs.file(mldsaPackedSo)
        .withPropertyName("mldsaPackedSo")
        .withPathSensitivity(PathSensitivity.NONE)
    from(mldsaBaselineSo) {
        rename { mldsaBaselinePackagedName }
    }
    from(mldsaPackedSo) {
        rename { mldsaPackedPackagedName }
    }
    into(jniLibsOut.map { it.dir("arm64-v8a") })
    doFirst {
        listOf(
            "mldsaBaselineSo" to mldsaBaselineSo.get(),
            "mldsaPackedSo" to mldsaPackedSo.get(),
        ).forEach { (property, input) ->
            require(input.isFile) {
                "$property must point to a prebuilt arm64-v8a libeu_id_ffi.so; " +
                    "set -P$property=/absolute/path/libeu_id_ffi.so"
            }
        }
    }
}

tasks.named("preBuild") {
    dependsOn(stageMldsaBenchLibraries)
}
