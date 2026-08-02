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

The final section of this file will record the same measurements after the
quality pass.
