# TS13 internal quality-pass benchmark

This record fixes the before-change baseline for the internal quality pass.
The benchmark calls the exported `prove_identity` and `verify_identity`
functions through `ts13_sdk_perf_probe`. Each sample uses a new process.

## Provenance

| Item | Value |
| --- | --- |
| Source commit | `3c676b1037dae56d40300a9aceafb706e208ca12` |
| Circuit artifact SHA-256 | `6b30e79449d331477027412fd30c831f7bb45cea42214b072845173fea0241b6` |
| Shape manifest SHA-256 | `a5c8c6fdbaac8e1a9b0ca81704b31c7e29f2ec27487f603139531c39faf42d60` |
| Generation-input SHA-256 | `60f05b9e596a48e03f6895f36f962775f3f6d1f2dfd50ca3fbb94640153863f0` |
| Mobile fixture SHA-256 | `06ef4ade577e1b69a776adafa778fd0fe16e3c75478772f1d5abf0c7072a98f4` |
| `Cargo.lock` SHA-256 | `23e70c964b943632fed547cfa38e6c1d24cfeac070a3518bc0f1a704f7597dbe` |
| `rust-toolchain.toml` SHA-256 | `8f0604004d13f7a26332366e59ba731bbb6046aaf789439d760abf67ad78589f` |
| Probe binary SHA-256 | `82482a3767f0e52c6280fe1e65b5dcc41c7a6c3d6380e034e92fd3395431c7f4` |

The host is an Arm64 Apple M2 Max MacBook Pro with 32 GB of memory. It runs
macOS 26.5.2. The compiler is Rust nightly 1.94.0 from 2026-01-14.

The release build used 12 build jobs:

```text
CARGO_BUILD_JOBS=12 cargo build --locked --release -j12 \
  -p sdk --example ts13_sdk_perf_probe
```

Each measured process used `RAYON_NUM_THREADS=12`. The canonical prover
selected six workers, a 2 MiB proof-thread stack, and a 16 MiB worker stack.

## Fresh-process samples

| Sample | Prove | Verify | Envelope |
| ---: | ---: | ---: | ---: |
| 1 | 1,218 ms | 41 ms | 1,572,910 bytes |
| 2 | 1,220 ms | 40 ms | 1,572,910 bytes |
| 3 | 1,336 ms | 41 ms | 1,572,910 bytes |
| 4 | 1,300 ms | 41 ms | 1,572,910 bytes |
| 5 | 1,372 ms | 42 ms | 1,572,910 bytes |
| 6 | 1,275 ms | 41 ms | 1,572,910 bytes |
| 7 | 1,345 ms | 41 ms | 1,572,910 bytes |
| Median | **1,300 ms** | **41 ms** | **1,572,910 bytes** |

The proof body is 1,572,864 bytes. The input fixture is 12,136 bytes.

One separate `/usr/bin/time -l` process measured a 1,235 ms proof, a 40 ms
verification, and a maximum resident set size of 1,509,670,912 bytes. Its
peak memory footprint was 1,348,535,808 bytes.

## Instrumented phase sample

This sample proved in 1,283 ms. Instrumentation changes timing, so these
values identify costs and do not replace the fresh-process baseline.

| Phase | Time |
| --- | ---: |
| Witness generation | 208.354 ms |
| Tree 0 write and commit | 31.731 ms |
| Tree 1 write and commit | 162.823 ms |
| Tree 2 write and commit | 456.685 ms |
| Post-interaction GKR | 148.123 ms |
| Post-interaction commit | 6.996 ms |
| STARK prove total | 259.904 ms |
| AIR core total | 1,072.281 ms |
| SDK core prove | 1,282.049 ms |
| Envelope encoding | 0.498 ms |

## Final result

The final source commit is
`48af5d6824201906bf7fd34a2207378243c788d4`. The artifact and fixture are
generated from that source.

| Item | Value |
| --- | --- |
| Circuit artifact SHA-256 | `a1011099bb0bd64358be0384940dd3afdd0ba23505107f26317fdf12599ea7ca` |
| Shape manifest SHA-256 | `3e9a04b651d4c624b68706a976fdb3f0167022a6770f5e53ec506e281b1ad1f0` |
| Generation-input SHA-256 | `9bec86696810221d688a00716e7a7a59af76b21a2be399eaa9c7794f0a9e2274` |
| Mobile fixture SHA-256 | `15bba3f244c9f36a4e1a09ff4b23373ff70784396d52a98267a89204f836de01` |
| `Cargo.lock` SHA-256 | `7bd6c3c4e9ac5048c8f33be56d0a8a2af9b7c4d909aa2101135294bd65bc8e99` |
| Probe binary SHA-256 | `ce65a663555637232a1fed183bacdcaf741d12365b425fd91c23503fda5d0b41` |
| Android AAR SHA-256 | `189b67abf5d61f94378733fb9929d24e1f80d334f894693bc19735f7e55cbb0b` |
| Android host APK SHA-256 | `30b8dd2103be571f17e80170d3cbb98c1da77b91da8159fc0b4b4e0adf20a56f` |
| Android test APK SHA-256 | `10b593f1516b4d47d130f6e3b7a22d454182c954ae4a14866676257475e7f570` |

The final samples used the same host, toolchain, fixture, process isolation,
and SDK worker settings as the baseline.

| Sample | Prove | Verify | Envelope |
| ---: | ---: | ---: | ---: |
| 1 | 1,219 ms | 40 ms | 1,507,374 bytes |
| 2 | 1,314 ms | 40 ms | 1,507,374 bytes |
| 3 | 1,325 ms | 40 ms | 1,507,374 bytes |
| 4 | 1,239 ms | 40 ms | 1,507,374 bytes |
| 5 | 1,264 ms | 40 ms | 1,507,374 bytes |
| 6 | 1,339 ms | 40 ms | 1,507,374 bytes |
| 7 | 1,339 ms | 40 ms | 1,507,374 bytes |
| Median | **1,314 ms** | **40 ms** | **1,507,374 bytes** |

The absolute prove median is 14 ms, or 1.1 percent, above the frozen baseline.
An alternating same-machine comparison measured a 1,323 ms baseline median
and a 1,328 ms final median. The 0.4 percent difference is inside run
variation, so this pass makes no latency-improvement or latency-regression
claim. The verify median decreased by 1 ms. The fixed proof body decreased by
65,536 bytes to 1,507,328 bytes. The public envelope remains fixed and
credential independent.

The final paired `/usr/bin/time -l` samples measured 1,516,847,104 baseline
bytes and 1,526,562,816 final bytes of maximum resident set size. The final
value is 0.6 percent higher. Peak memory footprint was 1,348,601,368 baseline
bytes and 1,332,233,728 final bytes. The counters move in opposite directions,
so this pass makes no memory-improvement claim.

One final instrumented sample measured 220.771 ms for witness generation,
31.084 ms for tree 0, 136.663 ms for tree 1, 444.318 ms for tree 2,
140.671 ms for post-interaction GKR, 258.652 ms for the STARK prover, and
1,024.764 ms for the AIR core. Instrumentation changes timing, so the
fresh-process medians are the performance result.

## Final verification

- All 535 normal release tests passed.
- All 18 ignored release tests passed.
- Release Clippy passed with warnings denied.
- Formatting, the all-target release build, the quantum-only dependency
  check, artifact drift, and `git diff --check` passed.
- The Android AAR built for Arm64 and x86-64. The release host and
  instrumentation APKs compiled against that AAR.
- Each native library in the host APK matched its AAR library byte for byte.
  The fixture in the instrumentation APK matched the checked-in fixture.
