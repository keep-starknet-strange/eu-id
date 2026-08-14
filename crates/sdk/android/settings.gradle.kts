// Build the Rust SDK, native libraries, bindings, and JNA runtime as one AAR.
// Publish the AAR to the local Maven repository.

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
