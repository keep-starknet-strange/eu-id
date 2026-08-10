// Packages the current host's Rust SDK library and generated UniFFI Kotlin
// bindings into the JVM test artifact consumed by the Android wallet.
plugins {
    kotlin("jvm") version "2.2.10"
    `maven-publish`
}

group = "com.kss"

val workspaceRoot = file("$projectDir/../../..")
val crateDir = file("$projectDir/..")
val uniffiConfig = file("$projectDir/../uniffi.toml")

val cargoVersion: String = run {
    val pkgSection = workspaceRoot.resolve("Cargo.toml").readText()
        .substringAfter("[workspace.package]").substringBefore("\n[")
    Regex("""(?m)^\s*version\s*=\s*"([^"]+)"""").find(pkgSection)?.groupValues?.get(1)
        ?: error("Could not find [workspace.package].version in ${workspaceRoot.resolve("Cargo.toml")}")
}
version = cargoVersion

val nativeLibsOut = layout.buildDirectory.dir("generated/uniffi/nativeLibs").get().asFile
val bindingsOut = layout.buildDirectory.dir("generated/uniffi/kotlin").get().asFile

data class HostNative(
    val jnaPrefix: String,
    val libraryFile: String,
)

val hostOs = System.getProperty("os.name").lowercase()
val hostArch = System.getProperty("os.arch").lowercase()
val isArm64 = hostArch.contains("aarch64") || hostArch.contains("arm64")
val hostNative = when {
    hostOs.contains("mac") || hostOs.contains("darwin") -> HostNative(
        if (isArm64) "darwin-aarch64" else "darwin-x86-64",
        "libeuid_zk_sdk.dylib",
    )
    hostOs.contains("win") && !isArm64 -> HostNative(
        "win32-x86-64",
        "euid_zk_sdk.dll",
    )
    hostOs.contains("linux") -> HostNative(
        if (isArm64) "linux-aarch64" else "linux-x86-64",
        "libeuid_zk_sdk.so",
    )
    else -> error("Unsupported JVM native host: $hostOs/$hostArch")
}

val toolBinDirs = listOf(
    "${System.getProperty("user.home")}/.cargo/bin",
    "/opt/homebrew/bin",
    "/usr/local/bin",
)
val toolPath = (toolBinDirs + (System.getenv("PATH") ?: "")).joinToString(File.pathSeparator)
val cargoExe = toolBinDirs.map { "$it/cargo" }.firstOrNull { file(it).exists() } ?: "cargo"
val cargoTargetDir = System.getenv("CARGO_TARGET_DIR")?.let { configured ->
    file(configured).let { if (it.isAbsolute) it else workspaceRoot.resolve(configured) }
} ?: workspaceRoot.resolve("target")
val hostLibrary = cargoTargetDir.resolve("release/${hostNative.libraryFile}")
val packagedLibrary = nativeLibsOut.resolve("${hostNative.jnaPrefix}/${hostNative.libraryFile}")

val cargoHostBuild by tasks.registering(Exec::class) {
    group = "rust"
    description = "Build the Rust SDK library for this JVM host."
    workingDir = workspaceRoot
    environment("PATH", toolPath)
    commandLine(cargoExe, "build", "--locked", "--release", "-p", "sdk")
    inputs.dir(crateDir.resolve("src"))
    inputs.file(crateDir.resolve("Cargo.toml"))
    inputs.file(workspaceRoot.resolve("Cargo.lock"))
    outputs.file(packagedLibrary)
    outputs.upToDateWhen { false }
    doFirst { delete(nativeLibsOut) }
    doLast {
        copy {
            from(hostLibrary)
            into(packagedLibrary.parentFile)
        }
    }
}

val generateUniffiBindings by tasks.registering(Exec::class) {
    group = "rust"
    description = "Generate UniFFI Kotlin bindings for the SDK crate."
    dependsOn(cargoHostBuild)
    workingDir = workspaceRoot
    environment("PATH", toolPath)
    doFirst { delete(bindingsOut) }
    commandLine(
        cargoExe, "run", "--locked", "--release", "-p", "sdk",
        "--features", "bindgen", "--bin", "uniffi-bindgen", "--",
        "generate",
        "--library", hostLibrary.absolutePath,
        "--language", "kotlin",
        "--config", uniffiConfig.absolutePath,
        "--out-dir", bindingsOut.absolutePath,
    )
    inputs.file(uniffiConfig)
    inputs.dir(crateDir.resolve("src"))
    inputs.file(crateDir.resolve("Cargo.toml"))
    inputs.file(hostLibrary)
    outputs.dir(bindingsOut)
}

sourceSets["main"].java.srcDir(bindingsOut)
sourceSets["main"].resources.srcDir(nativeLibsOut)

tasks.named("compileKotlin") { dependsOn(generateUniffiBindings) }
tasks.named("processResources") { dependsOn(cargoHostBuild) }

dependencies {
    api("net.java.dev.jna:jna:5.19.1")
    implementation(kotlin("stdlib"))
    testImplementation("junit:junit:4.13.2")
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
}
