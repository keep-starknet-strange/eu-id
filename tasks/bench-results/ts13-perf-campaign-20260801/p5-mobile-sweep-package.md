# P5 mobile runtime sweep package

Date: 2026-08-01

Privacy claim: `public-input unlinkable; transcript zero knowledge pending`

This checkpoint prepares one Android package pair for the P5 worker, stack,
affinity, and memory sweep. It has not uploaded the files or started a Firebase
matrix.

## Source checkpoints

- Product base: `cc7b7e75cedc30fd8cb3ab4f256c3714fc3d68de`
- Temporary controls: `c35a5213f652474e21ff823bf02dacfffdae2562`
- Source-bound artifact: `374f2946`
- Mobile fixture: `e2e65061`
- Temporary circuit hash: `74a94e63b80143190e5d7969db5fa3203dc462b41d7ce6ac1223650e071acb73`
- Proof body capacity: 1,572,864 bytes
- Proof envelope: 1,572,910 bytes

The temporary controls do not add an application API. The SDK still exports
only `proveIdentity` and `verifyIdentity`. The controls accept these values:

- proof thread stack: 64, 8, or 2 MiB;
- proof worker stack: 64, 48, 32, 24, or 16 MiB;
- Rayon workers: 1 through 16;
- optional `exclude_min_cluster` affinity policy.

The harness keeps each requested stack value through proof and verification.
It records success only after verification and both environment checks pass.
It then restores the previous process environment.

## Local verification

- The source-bound artifact check passed.
- The release A1/A2/B unlinkability test passed with 12 Rayon workers and one
  test-harness thread.
- The release fixture probe called `proveIdentity` and `verifyIdentity`.
- The probe measured 1,117 ms prove and 37 ms verify on the build computer.
- The SDK release tests passed 14 unit tests and two end-to-end tests.
- The Android helper tests passed.
- The fresh Android host and instrumentation sources compiled.
- The test APK fixture is byte-identical to the committed fixture.
- The host APK arm64 library is byte-identical to the AAR arm64 library.
- The arm64 library is a stripped AArch64 ELF shared object.
- The independent temporary-control review returned GO.

## SHA-256 values

- Cargo lock: `23e70c964b943632fed547cfa38e6c1d24cfeac070a3518bc0f1a704f7597dbe`
- Rust toolchain file: `8f0604004d13f7a26332366e59ba731bbb6046aaf789439d760abf67ad78589f`
- Generation input: `60f05b9e596a48e03f6895f36f962775f3f6d1f2dfd50ca3fbb94640153863f0`
- Shape manifest: `a5c8c6fdbaac8e1a9b0ca81704b31c7e29f2ec27487f603139531c39faf42d60`
- Circuit artifact: `74a94e63b80143190e5d7969db5fa3203dc462b41d7ce6ac1223650e071acb73`
- Generated Rust artifact: `e28880544aedc980a7177595364307830ac27bcd2ee0f382822e17f875f0d432`
- Release probe: `fb3c5a79564d7c46cfbe1de4c5f416987d6c800c2b2fc9ea8fb6ed445ecf1b5e`
- Fixture: `1adbc93e253c0bc46ec67b9be69c3d953e5f5e1741f08cf221dbcfdb68c41439`
- AAR: `d78d51e199661fd6e23a131d52354b0db3aaf2affc332504c4f52e0487d10738`
- Host APK: `9dd140d9ba9536fa9b8c5c1384217f50398db60f84f88f07e6c17e06e2f49e7f`
- Test APK: `b16b3add76d88907f0c0f44fc48e4fad33dca385d338a50d967f9547ccc1cbb3`
- AAR and host APK arm64 library:
  `7a3c3b5d49111f5027bd2fa0029be06dcf6d6b4c59077c0d2027f2bc832e36aa`

## Local package paths

- AAR: `/private/tmp/euid-p5-mobile-sweep-20260801-1/package/euid-zk-sdk-release.aar`
- Host APK: `/private/tmp/euid-p5-mobile-sweep-20260801-1/package/EuIdBenchAndroid-release.apk`
- Test APK: `/private/tmp/euid-p5-mobile-sweep-20260801-1/package/EuIdBenchAndroid-release-androidTest.apk`

The planned Firebase package prefix is
`ts13-unlinkable-v1-p5-runtime-sweep-package-20260801-1`. Every matrix will
reuse these exact two APK objects. Each matrix will run Pixel 8 (`shiba`),
Galaxy S24 Ultra (`e3q`), and Galaxy A54 (`a54x`) together on API 34.

## Planned matrices

The sweep uses no explicit CPU identifier. The first seven matrices use a
64 MiB proof thread stack and no affinity policy:

1. six workers and a 64 MiB worker stack;
2. four workers and a 64 MiB worker stack;
3. eight workers and a 64 MiB worker stack;
4. six workers and a 48 MiB worker stack;
5. six workers and a 32 MiB worker stack;
6. six workers and a 24 MiB worker stack;
7. six workers and a 16 MiB worker stack.

The campaign selects the smallest worker stack that completes proof and
verification on all three devices. It rejects a row after a crash, an invalid
result, a runtime-configuration mismatch, an envelope change, or a verification
failure.

The next two matrices use six workers and the selected worker stack:

8. an 8 MiB proof thread stack;
9. a 2 MiB proof thread stack.

The campaign selects the smallest proof thread stack that passes the same
checks. It then runs four fresh matrices in A/B/B/A order with the selected
stacks:

10. A1: six workers and no affinity policy;
11. B1: `exclude_min_cluster` affinity;
12. B2: `exclude_min_cluster` affinity;
13. A2: six workers and no affinity policy.

The affinity policy wins only when its mean prove time improves by more than
the larger within-pair difference on Pixel 8 and Galaxy S24 Ultra. Galaxy A54
must not regress by more than its within-pair difference. Each accepted row
must also keep verification at or below 350 ms and the proof envelope below
2,500,000 bytes.
