// Standalone Gradle build that packages the `sdk` Rust crate into a
// plug-and-play Android AAR (bindings + native libs + JNA), published to the
// local Maven repo. Kept separate from the Rust workspace so the SDK can be
// consumed by the wallet / verifier with a single dependency coordinate.

pluginManagement {
    repositories {
        google()
        mavenCentral()
        gradlePluginPortal()
    }
}

dependencyResolutionManagement {
    repositories {
        google()
        mavenCentral()
    }
}

rootProject.name = "euid-zk-sdk"
