# Android identity test host

This app runs `proveIdentity` and `verifyIdentity` on an Android device.
It consumes the AAR from `crates/sdk/android`. See the
[SDK build instructions](../../crates/sdk/android/README.md) for prerequisites.

Run all commands from the repository root. Build the AAR first:

```bash
./crates/sdk/android/gradlew -p crates/sdk/android assembleRelease
```

Build the host and instrumentation APKs:

```bash
./crates/sdk/android/gradlew -p mobile/EuIdBenchAndroid \
  assembleRelease assembleReleaseAndroidTest \
  -Pts13SdkAar=/absolute/path/to/euid-zk-sdk-release.aar
```

Run the APK pair in Firebase Test Lab:

```bash
gcloud firebase test android run \
  --type instrumentation \
  --app mobile/EuIdBenchAndroid/build/outputs/apk/release/EuIdBenchAndroid-release.apk \
  --test mobile/EuIdBenchAndroid/build/outputs/apk/androidTest/release/EuIdBenchAndroid-release-androidTest.apk \
  --test-targets class com.kss.euid.zk.sdk.Ts13MobileBenchmarkInstrumentedTest
```

The test logs one `Ts13MobileBenchmark` JSON record. The record includes prove
time, verify time, proof size, processor count, and peak resident memory.
