// Build the Rust SDK as a host-native desktop JVM test JAR.
// The local JAR contains only the current host's native library.
// It is not a cross-platform release artifact.
// The JAR lets wallet and verifier tests run without an Android target.
//
// `buildNative_<platform>` builds the native libraries.
// `generateUniffiBindings` creates the Kotlin bindings.
// The JAR contains the bindings and one host-native library.
// Maven Publish sends the test artifact only to the local Maven repository.
//
// Add this dependency to a JVM consumer:
//   testImplementation("com.kss:eu-id-zk-sdk-jvm:0.1.0")

plugins {
    kotlin("jvm") version "2.4.10"
    `maven-publish`
}

group = "com.kss"

repositories { mavenCentral() }

// Resolve the SDK crate and workspace from this project directory.
val workspaceRoot = file("$projectDir/../../..")
val uniffiConfig = file("$projectDir/../uniffi.toml")
val reproducibleBuild = workspaceRoot.resolve("scripts/reproducible-build.sh")
val allowDirtyBuild = providers.gradleProperty("allowDirtyBuild")
    .map(String::toBoolean)
    .getOrElse(false)

// Read the published version from `[workspace.package]`.
// This value keeps the JAR version equal to the Rust crate version.
val cargoVersion: String = run {
    val pkgSection = workspaceRoot.resolve("Cargo.toml").readText()
        .substringAfter("[workspace.package]").substringBefore("\n[")
    Regex("""(?m)^\s*version\s*=\s*"([^"]+)"""").find(pkgSection)?.groupValues?.get(1)
        ?: error("Could not find [workspace.package].version in ${workspaceRoot.resolve("Cargo.toml")}")
}
version = cargoVersion

val generatedKotlinDir = layout.buildDirectory.dir("generated/uniffi").get().asFile
val nativeLibsDir = layout.buildDirectory.dir("nativeLibs").get().asFile
val cargoTargetDir = System.getenv("CARGO_TARGET_DIR")?.let { configured ->
    File(configured).let { if (it.isAbsolute) it else workspaceRoot.resolve(configured) }
} ?: workspaceRoot.resolve("target")

// Add the common Cargo directory for Gradle processes.
val toolBinDirs = listOf(
    "${System.getProperty("user.home")}/.cargo/bin",
    "/opt/homebrew/bin",
    "/usr/local/bin",
)
val toolPath = (toolBinDirs + (System.getenv("PATH") ?: "")).joinToString(File.pathSeparator)
val cargoExe = toolBinDirs.map { "$it/cargo" }.firstOrNull { file(it).exists() } ?: "cargo"
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

// Map each Rust target to its JNA path and library file.
data class NativeTarget(
    val rustTarget: String,
    val jnaPrefix: String,
    val libFile: String,
)

// Detect the host one time.
// A macOS host must build the Apple targets.
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

val hostNativeTarget = when ("$HOST_OS-$HOST_ARCH") {
    "macos-arm64" -> NativeTarget(
        "aarch64-apple-darwin",
        "darwin-aarch64",
        "libeuid_zk_sdk.dylib",
    )
    "macos-x86_64" -> NativeTarget(
        "x86_64-apple-darwin",
        "darwin-x86-64",
        "libeuid_zk_sdk.dylib",
    )
    "linux-arm64" -> NativeTarget(
        "aarch64-unknown-linux-gnu",
        "linux-aarch64",
        "libeuid_zk_sdk.so",
    )
    "linux-x86_64" -> NativeTarget(
        "x86_64-unknown-linux-gnu",
        "linux-x86-64",
        "libeuid_zk_sdk.so",
    )
    "windows-x86_64" -> NativeTarget(
        "x86_64-pc-windows-msvc",
        "win32-x86-64",
        "euid_zk_sdk.dll",
    )
    else -> error("Unsupported JVM native host: $HOST_OS-$HOST_ARCH")
}
val nativeTargets = listOf(hostNativeTarget)

val buildNativeTasks = nativeTargets.map { t ->
    tasks.register<Exec>("buildNative_${t.jnaPrefix.replace('-', '_')}") {
        group = "rust"
        description = "Build ${t.rustTarget} -> ${t.jnaPrefix}/${t.libFile}"
        workingDir = workspaceRoot
        environment("PATH", toolPath)
        val dirtyArgument = if (allowDirtyBuild) listOf("--allow-dirty") else emptyList()
        if (t.rustTarget.endsWith("apple-darwin")) {
            val targetName = t.rustTarget.uppercase().replace('-', '_')
            environment(
                "CARGO_TARGET_${targetName}_RUSTFLAGS",
                "-C link-arg=-Wl,-install_name,@rpath/${t.libFile}",
            )
        }
        commandLine(
            listOf("bash", reproducibleBuild.absolutePath) + dirtyArgument + listOf(
                cargoExe, "rustc", "--locked", "--offline", "--release", "-p", "sdk", "--lib",
                "--target", t.rustTarget, "--crate-type", "cdylib",
            ),
        )

        inputs.property("allowDirtyBuild", allowDirtyBuild)
        inputs.files(rustWorkspaceInputs).withPathSensitivity(PathSensitivity.RELATIVE)
        val builtLib = cargoTargetDir.resolve("${t.rustTarget}/release/${t.libFile}")
        val destDir = File(nativeLibsDir, t.jnaPrefix)
        val packagedLib = File(destDir, t.libFile)
        outputs.files(builtLib, packagedLib)
        doFirst { project.delete(packagedLib) }
        doLast { copy { from(builtLib); into(destDir) } }
    }
}

// Read the UniFFI metadata from the host library.
val hostNativeTask = buildNativeTasks.single()
val hostLib = cargoTargetDir.resolve(
    "${hostNativeTarget.rustTarget}/release/${hostNativeTarget.libFile}",
)

val generateUniffiBindings by tasks.registering(Exec::class) {
    group = "rust"
    description = "Generate UniFFI Kotlin bindings for the sdk crate."
    dependsOn(hostNativeTask)
    workingDir = workspaceRoot
    environment("PATH", toolPath)
    val dirtyArgument = if (allowDirtyBuild) listOf("--allow-dirty") else emptyList()
    commandLine(
        listOf("bash", reproducibleBuild.absolutePath) + dirtyArgument + listOf(
        cargoExe, "run", "--locked", "--offline", "-p", "sdk", "--features", "bindgen", "--bin", "uniffi-bindgen", "--",
        "generate",
        "--library", hostLib.absolutePath,
        "--language", "kotlin",
        "--config", uniffiConfig.absolutePath,
        "--out-dir", generatedKotlinDir.absolutePath,
        ),
    )
    inputs.property("allowDirtyBuild", allowDirtyBuild)
    inputs.files(rustWorkspaceInputs).withPathSensitivity(PathSensitivity.RELATIVE)
    inputs.file(uniffiConfig).withPathSensitivity(PathSensitivity.RELATIVE)
    inputs.file(hostLib).withPathSensitivity(PathSensitivity.NONE)
    outputs.dir(generatedKotlinDir)
    doFirst { project.delete(generatedKotlinDir) }
}

// Add the generated Kotlin bindings and native libraries to the JAR.
sourceSets["main"].java.srcDir(generatedKotlinDir)
sourceSets["main"].resources.srcDir(nativeLibsDir)

tasks.named("compileKotlin") { dependsOn(generateUniffiBindings) }
tasks.named("processResources") { dependsOn(buildNativeTasks) }

dependencies {
    // Export the JNA-based UniFFI runtime to consumers.
    api("net.java.dev.jna:jna:5.19.1")
    implementation(kotlin("stdlib"))
    testImplementation(kotlin("test"))
}

tasks.withType<AbstractArchiveTask>().configureEach {
    isPreserveFileTimestamps = false
    isReproducibleFileOrder = true
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
    // `publishToMavenLocal` writes to the local Maven repository.
}
