# P4 blowup-three Android packages

Date: 2026-08-01

Privacy claim: `public-input unlinkable; transcript zero knowledge pending`

This pass prepared the four valid blowup-three Android package pairs. It did
not upload an APK. It did not start a Firebase test.

## Fixed build inputs

- Android benchmark harness: `5562c33c44bc1d2cbd119f9ebab0e40e94512b93`
- Output root: `/private/tmp/euid-p4-android-b3-20260801`
- Rust: `rustc 1.94.0-nightly (86a49fd71 2026-01-14)`
- Cargo NDK: `cargo-ndk 4.1.2`
- Gradle: `9.5.0`
- Android Gradle Plugin: `9.2.1`
- NDK: `27.1.12297006`
- Cargo lock SHA-256: `23e70c964b943632fed547cfa38e6c1d24cfeac070a3518bc0f1a704f7597dbe`
- Rust toolchain file SHA-256: `8f0604004d13f7a26332366e59ba731bbb6046aaf789439d760abf67ad78589f`
- Shape manifest SHA-256: `a5c8c6fdbaac8e1a9b0ca81704b31c7e29f2ec27487f603139531c39faf42d60`
- Cargo jobs: `6`
- Probe Rayon workers: `12`
- Probe environment `RUST_MIN_STACK`: `536870912` bytes
- Effective proof and worker stacks: `67108864` bytes
- Enabled proof-package features: none

The harness files have no difference from the harness commit. The build used a
scratch copy of `mobile/EuIdBenchAndroid`. The product worktree did not change.

## Source-bound checkpoints

| Point | Source commit | Artifact commit | Generation input SHA-256 | Soundness source SHA-256 | Circuit hash | Body bytes | Envelope bytes |
| --- | --- | --- | --- | --- | --- | ---: | ---: |
| q36/p20/L19 | `4e14f09df39f2820f3c2eaffe433a16ad62b9b2a` | `95e5f9a820904e32abb39a3eedfcf04f52cf88be` | `60f05b9e596a48e03f6895f36f962775f3f6d1f2dfd50ca3fbb94640153863f0` | `bc6171874fd1383c6dfc457af3301b5c36b24d8e5201f96f35162c124e9111c3` | `4d55b4e5cb6d4fab102395d3647d267d3f3116e6cabae9e33f3c957f7e07c2b2` | 1,572,864 | 1,572,910 |
| q36/p20/none | `edde21bbe0fff0a42666e278940a933631e03925` | `269d5854a7aa9c3532f2bb1c9dc8540122d15615` | `b7e4fd6cfd1c610b5c61ca588acfdf7f46bd013802d7b96ebbc24c23d3b0bbed` | `9dcd0c6afe0a5ff34572abec084eb2bf6b7260f888cf90e30a7887865eae9566` | `f5b6e13df0405190b5715b4bb8c4d5313dd4c22149167e5b23bceba03289717c` | 1,507,328 | 1,507,374 |
| q35/p23/none | `c9f45da8ac65066d8b6e9d19b88dfe3f9be32a5d` | `382eadec1046751c575e6754148c8d4316c31815` | `9d38f038cdec98acf5392c90f0f0fcd8562f290df3532786c2eb1efb4963e4e9` | `593fec9bcdb7f94686512dd50d603d7b0f873c3f3e55c6e2768d0d7d0d50ec7b` | `23463f054d71ba16f908b6aa61eba48eca1b6795b48ec324ed1bd160a8950222` | 1,507,328 | 1,507,374 |
| q35/p23/L19 | `1777c39b402646bd50e4510b1e507b36e7979dfe` | `9f976ad59d1da0d9097ce65a247ff4eaf12d2476` | `4c345eef8c32665822fe080c853e1c907e11ca5ec33f35ce8b07d713e5284379` | `06905301a86b4015104c5034c44fffaf218946e790f7c154a044d41dfc9be2c6` | `e6fd40594e446dd70c45598bd8e82d58d8dfb86722aa81714460c748d4e59668` | 1,507,328 | 1,507,374 |

For every row, the circuit hash is also the SHA-256 of
`circuit-artifact-v1.cbor`.

## Package SHA-256 values

### q36/p20/L19

Path: `/private/tmp/euid-p4-android-b3-20260801/q36-p20-l19`

- AAR: `8e53ecfddb047e0be8a958a71eee2472b8a1f3d5d367238d3c83922b9dd318bd`
- Fixture: `ad775e87c9369b85e707025bf8f909715e2fc4de97e3db8005e10317bdbf8863`
- Host APK: `372ccb129256e479a61f53bae3305c424c11c0c905f4fdda2320f5f7de86d1be`
- Test APK: `287be0265632bec74bd450edc53fdc96475329316e54d936016e9b07ef115ca0`
- AAR and host APK arm64 library: `3d837de9e06f3f5895fa437a2b00e83fc1c0065080fc24fc4d6742dafb6da27c`

### q36/p20/none

Path: `/private/tmp/euid-p4-android-b3-20260801/q36-p20-none`

- AAR: `d8735b32d0ca440f5b1c8f6da369cd064c027341f334c04943fe25e59257718a`
- Fixture: `2547fde14734b63d2f2f75001091e779d5ec8470563ca75a6d0ff8168a33139c`
- Host APK: `88635b8892e5d718d435ca4202e9ca5380f2dbf10eea563f398e06406b2c7bfe`
- Test APK: `5d3278eaaa67e26d17802ccb45b811e79ce8c753f7cb5f682872de156b7c0549`
- AAR and host APK arm64 library: `fcab91edad62a1b6f1dfeedfbf0811654bdbdd02218a62f42b2ea22fbe79bc2a`

### q35/p23/none

Path: `/private/tmp/euid-p4-android-b3-20260801/q35-p23-none`

- AAR: `fff52e1e17e0fbfede9d3360421d290e7e402307a2e0f47a7dadd78979a9e85f`
- Fixture: `07697a43ce29af16effaf1cf280843485efab6a994b1a40d8b2aa45aee12d4a1`
- Host APK: `dff4225b19f2d33ae05bdcf13a95097f3aa0751df802c3da9f35026f6f4c549e`
- Test APK: `5fbe7ea95a33c92757805bd79463a73f46e3143807199c495b8e2984ca396807`
- AAR and host APK arm64 library: `cdb6fd3b52e92cea69836a84efbb85e806847577cfa794cf2ebe8bbe6feb3580`

### q35/p23/L19

Path: `/private/tmp/euid-p4-android-b3-20260801/q35-p23-l19`

- AAR: `ff10ab49dbaac9445ef923bf29a98818754f867e2605397f6204fdb9a250288f`
- Fixture: `4837074af336f5c160f62056cd91fe5b2b5d6e2e8760acaa5da2c60af80c5d39`
- Host APK: `23cf0edbf27f2d8f513ba9c047b7a7351c86040a0ef2a8662eb5e984b8996ced`
- Test APK: `a4f84b346e99e2c6e66d3f1826fb59bd271534f95c51777d90bc5901f4d74fbb`
- AAR and host APK arm64 library: `d7d6d458a6fdb667b3d860770bc88d82d56b9266bcfbaaa481b24e589176ce54`

## Build commands

The build ran these commands for each table row. `ARTIFACT` and `CONFIG` are
the exact values in the tables above.

```text
rtk git switch --detach ARTIFACT
rtk proxy env CARGO_BUILD_JOBS=6 RAYON_NUM_THREADS=12 RUST_MIN_STACK=536870912 CARGO_TARGET_DIR=/private/tmp/euid-p4-android-b3-target cargo run --locked --release -j6 -p sdk --example ts13_sdk_perf_probe -- --iterations 1 --fixture-out /private/tmp/euid-p4-android-b3-20260801/CONFIG/ts13_mobile_benchmark_fixture_v1.json
rtk proxy env CARGO_BUILD_JOBS=6 CARGO_TARGET_DIR=/private/tmp/euid-p4-android-b3-target JAVA_HOME=/Applications/Android\ Studio.app/Contents/jbr/Contents/Home ANDROID_HOME=/Users/lucas/Library/Android/sdk ./crates/sdk/android/gradlew -p crates/sdk/android --no-daemon assembleRelease
rtk proxy env JAVA_HOME=/Applications/Android\ Studio.app/Contents/jbr/Contents/Home ANDROID_HOME=/Users/lucas/Library/Android/sdk crates/sdk/android/gradlew -p /private/tmp/euid-p4-android-b3-harness --no-daemon assembleRelease assembleReleaseAndroidTest -Pts13SdkAar=/private/tmp/euid-p4-android-b3-20260801/CONFIG/euid-zk-sdk-release.aar
```

The first harness build also ran `testReleaseUnitTest`. It passed 16 tests.
It had zero failures, zero errors, and zero skipped tests.

## Verification

Each exact-checkpoint release probe called the canonical `proveIdentity` and
`verifyIdentity` path. Each proof verified before the probe wrote the fixture.
The probes reported these smoke-test times: 1,315/36 ms, 1,314/37 ms,
1,318/41 ms, and 1,453/39 ms for prove/verify in table order. These values are
not campaign performance results because other work used the host.

The final package matrix ran 12 automated checks. All 12 checks passed. Four
separate ELF checks also passed.

- The fixture in each test APK has the same bytes as its persisted fixture.
- The arm64 library in each host APK has the same bytes as the stripped arm64
  library in its AAR.
- Each arm64 library is a stripped AArch64 ELF shared object.
- Each fixture has its checkpoint circuit hash.
- Each fixture names `proveIdentity` and `verifyIdentity`.
- Each fixture has the exact privacy claim at the top of this report.

The AAR build also contains an x86-64 library. The package pair is ready for an
arm64 Firebase device run.

## Failures and warnings

No proof failed. No AAR build failed. No APK build failed. No package check
failed.

UniFFI could not find `ktlint` for generated binding formatting. The build used
the generated binding without this optional formatting step. The app package
task reported that it could not strip its input native library. The AAR package
had already stripped the library. The final ELF check confirmed the stripped
library in each host APK.
