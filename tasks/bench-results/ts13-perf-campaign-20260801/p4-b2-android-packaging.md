# P4 blowup-two Android packages

Date: 2026-08-01

Status: complete. This task built and checked six offline Android package
pairs. It did not upload an APK. It did not run Firebase Test Lab.

The privacy claim is `public-input unlinkable; transcript zero knowledge pending`.
All roles use ML-DSA-65. The fixture names `proveIdentity` and
`verifyIdentity`. This task did not change the product API.

## Fixed inputs

- Android harness commit:
  `5562c33c44bc1d2cbd119f9ebab0e40e94512b93`
- Package root: `/private/tmp/euid-p4-android-b2-20260801`
- Android ABIs: `arm64-v8a` and `x86_64`
- Android NDK: `27.1.12297006`
- Android compile SDK: `36`
- Cargo profile: locked release
- Maximum Cargo jobs: `6`
- Maximum Gradle workers: `6`
- Probe Rayon workers: `6` per packaging job
- Concurrent b2 and b3 probe limit: `12` host Rayon workers in total
- SDK proof-thread stack: `67108864` bytes
- SDK proof-worker stack: `67108864` bytes
- Probe wrapper-thread stack: `33554432` bytes
- Command-only `RUST_MIN_STACK` request: `536870912` bytes
- Shared Cargo target:
  `/private/tmp/euid-p4-android-b2-20260801/b2-q54-p20-none/cargo-target`

The shared Cargo target reduced rebuild time. Cargo checked its source
fingerprints after each exact Git checkout. Gradle ran `clean`,
`--rerun-tasks`, and `--no-build-cache` for every AAR. Each candidate has a
different arm64 library hash.

The SDK sets its proof-thread and proof-worker stacks explicitly. Therefore,
the `RUST_MIN_STACK` environment value did not set those stack sizes. The b2
and b3 packaging jobs ran at the same time. Each job requested six Rayon
workers, which limited the two jobs to 12 host Rayon workers in total.

## Source and probe ledger

| Lift | Queries | PoW | Source commit | Artifact commit | Generation input SHA-256 | Circuit hash | Probe SHA-256 |
| ---: | ---: | ---: | --- | --- | --- | --- | --- |
| None | 54 | 20 | `cd4567370d0967a45cf1886e75c88443bc3f866f` | `e56bd8a7fde21417fc63335452e49732fe167c54` | `0b1a32399ce8f8b9871df5c70c1786d869be87c3ddc2e9eaf8398f00e279ec51` | `6ffaf7fa2274b5d486c79c5504c340f3bcd9004f7f4aa7523a731e8c27e62368` | `c2ddab5c36742737c0ddd5c63f9d14cf058ed68a8978faf5755e10c7dcadcb99` |
| None | 53 | 22 | `18b8fc73218156ccb37c49b3c176c0a4a54789f1` | `895b3833c16eee87a549467ee576cb8136803a03` | `849e3057c8dc10432612a7eecf3c0f3d0d8b1a6506d112d56b81a1eb96d4d854` | `fd77e8d34592bc6b06cfb690dd25a98dbed61c1c0ea561a231eaf7b3781cd724` | `ede465e6bbbf98d428b63f8e103e9dd6d9aaa15a7ceb16a92a5cb3c510af982b` |
| None | 52 | 24 | `d3da76c13d2c99a552e93905704070b9a1b501a7` | `103b289464df151f53b51ba7602d2004c9e64773` | `c9a88cccf576c3bd0060b5c6a25bd2018f6eccc42ecb54a0112c8da0d77dfea1` | `e4931cbdc3499a614aafdf1c140561736629895c1369836bce521703ecd36d3f` | `b74c291196c69e0219327a2e54ee2aa33e3127d1a98c62532b5dc0541240cf44` |
| 18 | 54 | 20 | `681d0bb76745a34add73f4a711c7da0cf93c07e9` | `0b2c0de6dd9480d86b9327571df9028b08032cbd` | `cbde428631ab86c80c126766c099f1a4702b705f54ef281ace5aab2232e0599c` | `7a1ffb8f0e38dc5a97d1ca49d19c4e1f7cea32a4ff612cbe4299a226f9fd3303` | `5d6040c031d3ac929bc190e3f68cc6b840804b233ea5b6e58e946e3ada28c5a1` |
| 18 | 53 | 22 | `2222ca175bfbdbb7dc82eb02a2c6922f22590a0c` | `9ece1fabb3e3d907842b4b4f61dd21890d731ec4` | `3c2d92686af595c72368e1030f526e8f20ae9f5d436cabcfc97c56aede41ea62` | `3da0d201333316da2bb8243812d7980e21f18b45b9283bf284da686c7f1dd800` | `21457168526a31d0e53adfa2dede20f876acef775ea4f87b7cafd45ba26abb3a` |
| 18 | 52 | 24 | `ce2a42e71210de9ca37da32eb9609ecb162390b0` | `0ebc4a5e0a1f6d028ae7958dbe343bb621449b8e` | `5b2e10b4ec4e1d9a61dec38f47d115ea29599826f8b1b06369236f0cf4ea15eb` | `e7150917a9144f67d9036505fa0a0b1004db8c64f2fe81b86fc0c337b18942b2` | `8eeff34ab76f312ccbfbefa267bbeb35aa612fd55fea979bb3f22686833188c3` |

For each row, the artifact commit has the source commit as its first parent.
The worktree had no tracked change before the AAR build. The probe SHA-256
matched the desktop frontier ledger before fixture generation.

## Package ledger

| Directory | AAR SHA-256 | Fixture SHA-256 | Host APK SHA-256 | Test APK SHA-256 | arm64 library SHA-256 |
| --- | --- | --- | --- | --- | --- |
| `b2-q54-p20-none` | `5919cccf8dcaae55b19db4c8477e1e5d26b2b15d7330450cd400f0a1a5e620b0` | `ecaa6c45b7194ab1af111e21c0e6b43da8c810c1a1a845aac903629b67c2369f` | `7ecfb86df6827836d13b9c35996be5913c01b30a9cf73af8d051120a22a34d49` | `94b3e1ec8a2e22d8834a3ac5312702fe7971bd8ffd21e736a6ae51e7be7a0316` | `b8d9c7afec2fc16e6a6d2b94b39646c8cb4c66b5a67a0124ef381c513f843eea` |
| `b2-q53-p22-none` | `ee8f86cd6e7557cd59b25f6e03525d4febb22c58703a9b4f97be0f673dc1193c` | `571a3762abc986ac02e9807d17512e716ecc30de993c0d87b36f4cdb1b9b4a85` | `34a3755ab25ce7a90217ddb7c35b0746001d9bd803239a901083dad76caf5058` | `0e2e87f0d0b569529501f0bd18e18dabfc2a2db6fd263cdcfd10495b780fde2c` | `5a4dd9b40e4fcc8fb9f4fa78a43a64dc67017373550736c15b3ae271c290406c` |
| `b2-q52-p24-none` | `d657f426fed8d442dd316e1838f2f915fffddba6e6c594fbd2f8408c8e453583` | `81e410939b675feaddf5b0270a2affd563d778198a1df36258dfbe025bf7e257` | `55f4c30800ee9b815e3a17f580e4c142eab82b34c727b916f985e21dc935431e` | `52d3c48362fbfc5afa5c5a983f0ff6adeabf51151a79ae0dcaed4e871578a5f9` | `1714e99db150f23137013429bd8afee2136f9e67440f964fcef4c20656fbab42` |
| `b2-q54-p20-l18` | `58db60b607638d5256bd50c6c2397253a3fc3112ec4b0323e6feb73381770a70` | `306876d618c24b58f45f56cbc408bc4632def90d703d9d9f9fa7d3f309b175f5` | `0c19fc2343c9d2d013be942c00c619b3be2ded05b94724b778b14747ff82cfcc` | `172a34b844ef4b2d2eba838f241e0db2e08fbd77f266c62b53f0615045280e27` | `9a3f40bb6e19ecbc957bbfed81d60408fc1bbe486c8f62dc6a28240fd7a219d0` |
| `b2-q53-p22-l18` | `b7419dd6f3f1b26cf2bdfa4256f93df4e6f590c733c0b56954a76a99125c6752` | `4ab3e3d087e23370be9f8d6489dd4320b2274162223bcfb6001d31400be10ec7` | `39485c693751ffbf24b4cabcbf37046cf6ca46ca60b20df48934059564430650` | `9f82903ed195e32862251517c109adf705150d447323f05c986927fa381898b8` | `e8c78fe3302721a3557fdc86f51cab80fc06fb68d434c65d67c2a2075fdc7178` |
| `b2-q52-p24-l18` | `22a2d596a8c276422641d95fe2f82ba552e6650f3d0a43505b3bc5311c1df2a4` | `09b42787be0b77bb946d3730d8af5bbbe50d42836d21ce00d32743cf65265ec0` | `0a0f4163171457db188a3706e623ea0bbafc638d6a73ebc3dcd9b8cb729b162a` | `94a36e79a04f37e322bc05cab0031a4ec14e4f17909b05781eb02a1d5ea0e9d8` | `00940e440801ceeca12a3b708dccad9403762d724656829ac367896c73eefe88` |

Each directory contains these files:

- `euid-zk-sdk-release.aar`
- `ts13_mobile_benchmark_fixture_v1.json`
- `EuIdBenchAndroid-release.apk`
- `EuIdBenchAndroid-release-androidTest.apk`

The `verify` subdirectory contains the extracted fixture and arm64 libraries
that the checks used.

## File sizes

| Directory | AAR | Fixture | Host APK | Test APK |
| --- | ---: | ---: | ---: | ---: |
| `b2-q54-p20-none` | 6,720,283 B | 40,035 B | 18,361,258 B | 711,119 B |
| `b2-q53-p22-none` | 6,720,274 B | 40,035 B | 18,361,258 B | 711,119 B |
| `b2-q52-p24-none` | 6,720,278 B | 40,035 B | 18,361,258 B | 711,119 B |
| `b2-q54-p20-l18` | 6,720,323 B | 40,035 B | 18,361,258 B | 711,119 B |
| `b2-q53-p22-l18` | 6,720,295 B | 40,035 B | 18,361,258 B | 711,119 B |
| `b2-q52-p24-l18` | 6,720,341 B | 40,035 B | 18,361,258 B | 711,119 B |

## Build commands

The task checked out each artifact commit before this AAR command:

```text
rtk git switch --detach ARTIFACT_COMMIT
rtk proxy env JAVA_HOME='/Applications/Android Studio.app/Contents/jbr/Contents/Home' ANDROID_HOME=/Users/lucas/Library/Android/sdk CARGO_BUILD_JOBS=6 CARGO_TARGET_DIR=/private/tmp/euid-p4-android-b2-20260801/b2-q54-p20-none/cargo-target ./crates/sdk/android/gradlew -p crates/sdk/android clean assembleRelease --rerun-tasks --no-build-cache --no-daemon --max-workers=6 --console=plain
```

The exact verified probe generated the candidate fixture:

```text
rtk proxy env RAYON_NUM_THREADS=6 RUST_MIN_STACK=536870912 PROBE --iterations 1 --fixture-out CANDIDATE_DIRECTORY/ts13_mobile_benchmark_fixture_v1.json
```

The task put the generated fixture in the exact harness source. It compared
the source fixture SHA-256 with the generated fixture SHA-256 before this APK
command:

```text
rtk proxy env JAVA_HOME='/Applications/Android Studio.app/Contents/jbr/Contents/Home' ANDROID_HOME=/Users/lucas/Library/Android/sdk CARGO_BUILD_JOBS=6 ./crates/sdk/android/gradlew -p mobile/EuIdBenchAndroid clean assembleRelease assembleReleaseAndroidTest -Pts13SdkAar=CANDIDATE_DIRECTORY/euid-zk-sdk-release.aar --rerun-tasks --no-build-cache --no-daemon --max-workers=6 --console=plain
```

The first package build also ran `testReleaseUnitTest`. It passed. The harness
source was identical for the other five builds.

## Verification

All six candidates passed these checks:

1. The artifact commit and its source parent matched the source ledger.
2. The persistent probe SHA-256 matched the probe ledger.
3. The probe completed one release `proveIdentity` and `verifyIdentity` run.
4. The probe wrote the mobile fixture.
5. The fixture circuit hash matched the source-bound circuit artifact.
6. The fixture named only `proveIdentity` and `verifyIdentity`.
7. The fixture used the exact privacy claim in this report.
8. The release AAR build completed for both Android ABIs.
9. The release host APK and release test APK builds completed.
10. The fixture extracted from the test APK was byte-for-byte equal to the
    generated fixture.
11. The arm64 library extracted from the host APK was byte-for-byte equal to
    the arm64 library in the AAR.
12. Each arm64 library was a stripped AArch64 ELF shared object.

The probe runs were build checks. The b2 and b3 packaging jobs used the host
at the same time. They could use 12 Rayon workers in total. Do not use their
latency values to select the PCS point.

## Warnings and discarded checks

- The first sandboxed Gradle command could not create the existing Gradle
  wrapper lock file. It stopped before the build. The approved rerun used the
  existing Gradle cache and passed.
- The sandbox did not permit a direct file copy into the tracked fixture.
  The task first proved that the generated file differed only in the fixture
  name and circuit hash. It then used `apply_patch`. The complete SHA-256
  values matched before every APK build.
- The first streamed ZIP hash check did not pass bytes through the RTK
  pipeline. It produced an empty-input hash and a broken-pipe error. This
  result is not evidence. The task extracted each payload, compared it with
  `cmp`, and hashed the extracted file.
- UniFFI reported that `ktlint` was not installed. Binding generation and all
  Gradle tasks completed. This warning did not change a package check.
- The host package task reported that it could not strip the two libraries.
  The candidate SDK library was already stripped in the AAR. The extracted
  host library matched it exactly.

No candidate AAR build, fixture proof, APK build, or extracted-payload check
failed.
