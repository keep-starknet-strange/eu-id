plugins {
    id("com.android.application") version "9.2.1"
}

val sdkAar = providers.gradleProperty("ts13SdkAar")
    .map(::file)
    .orElse(file("../../crates/sdk/android/build/outputs/aar/euid-zk-sdk-release.aar"))

dependencies {
    implementation(files(sdkAar))
    implementation("net.java.dev.jna:jna:5.19.1@aar")
    androidTestImplementation("androidx.test.ext:junit:1.3.0")
    androidTestImplementation("androidx.test:runner:1.7.0")
    testImplementation("junit:junit:4.13.2")
}

android {
    namespace = "eu.euid.bench"
    compileSdk = 36
    testBuildType = "release"

    defaultConfig {
        applicationId = "eu.euid.bench"
        minSdk = 24
        targetSdk = 36
        versionCode = 1
        versionName = "1.0"
        testInstrumentationRunner = "androidx.test.runner.AndroidJUnitRunner"
        ndk {
            abiFilters += listOf("arm64-v8a", "x86_64")
        }
    }

    buildTypes {
        release {
            isMinifyEnabled = false
            signingConfig = signingConfigs.getByName("debug")
        }
    }
}

tasks.named("preBuild") {
    doFirst {
        require(sdkAar.get().isFile) {
            "Build the SDK AAR or set -Pts13SdkAar=/absolute/path/to/sdk.aar"
        }
    }
}
