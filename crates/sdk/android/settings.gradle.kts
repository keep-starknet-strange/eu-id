// This standalone Gradle build packages the Rust SDK, Kotlin bindings, and
// native libraries in an Android AAR. The Maven publication declares JNA as a
// transitive dependency. An application can use one dependency coordinate.

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
