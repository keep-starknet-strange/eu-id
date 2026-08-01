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

Use private test arguments to request a worker count or an explicit CPU mask.
Firebase names the flag `--environment-variables`. It sends the values to
AndroidJUnitRunner. Use `+` between CPU identifiers because the flag uses
commas between arguments:

```bash
--environment-variables rayon_threads=6,affinity_cpu_ids=4+5+6+7
```

Use this argument to test the affinity policy:

```bash
--environment-variables affinity_policy=exclude_min_cluster
```

Do not use `affinity_cpu_ids` and `affinity_policy` in the same test. The
policy reads `cpu_capacity` for each allowed CPU. If this data is incomplete,
the policy reads `cpuinfo_max_freq` for each allowed CPU. It removes the
minimum tier and selects a maximum of six CPUs. If the topology or the affinity
system call is not available, the test keeps the original CPU mask.

When the policy is active, the test sets the worker count to the smaller of
the requested count and the selected CPU count. It uses the selected CPU count
when no count is requested. The worker count cannot exceed six. If the policy
is not active, the test uses only the requested worker count.

The CPU mask applies only to the benchmark thread. The proof thread and its
workers inherit the mask. The SDK API does not expose affinity controls.

The test logs one `Ts13MobileBenchmark` JSON record. The record includes prove
time, verify time, proof size, requested, configured, and actual worker counts,
the worker-count source, proof and worker stack sizes, phase memory samples,
CPU topology, the policy decision, the effective CPU mask, and peak resident
memory.
