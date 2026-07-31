# Canonical TS13 desktop performance campaign

Date: 2026-07-31

This report measures the canonical `proveIdentity` path.
The privacy claim is `public-input unlinkable; transcript zero knowledge pending`.
The report does not claim that STWO is zero knowledge.

## Provenance

- Source commit: `bf5c5075386fd7706f5489d1ecebb602ea2e3e7f`
- Branch: `codex/ts13-unlinkable-v1`
- Circuit hash: `9772642c038b0b34c2bbbe2d6a72d11f3d4a954c696a5bacccd5d15ed4974ad9`
- Shape manifest SHA-256: `fbe394a6f265b06589db03f1e31a353203b0707e290eaba8aecf78ab1a77b748`
- Soundness source-tree SHA-256: `a768f9673ae604cb8d0c689be8c65803432aaa8a2f37373bf80517dc20660eed`
- Cargo.lock SHA-256: `73debb317fa1c70400395f3ddcca8f8e24b85d3cf699a9b82dc286b4415b1fe8`
- Proof-body capacity: 1,638,400 bytes
- Identity-proof envelope: 1,638,446 bytes
- Query count: 36
- Tree column counts: `[310, 4868, 2400, 8, 32]`

The source tree was clean before the benchmark binary and Android artifacts were built.
The full release test matrix, the ignored slow proof matrix, Clippy, formatting, and the artifact drift check passed.

## Desktop method

The host was a MacBook Pro with an Apple M2 Max, 12 CPU cores, and 32 GB RAM.
The operating system was macOS 26.5.2, build 25F84.
The Rust compiler was `rustc 1.94.0-nightly (86a49fd71 2026-01-14)`.

Each cold sample used a fresh process and one `proveIdentity` call.
Each process used `RAYON_NUM_THREADS=12` and `RUST_MIN_STACK=536870912`.
The sample order was counter-ordered between timing enabled and timing disabled.
`/usr/bin/time -l` measured the process peak resident set size.
The benchmark invoked the release binary directly, so it did not include Cargo or link time.

The timing-enabled samples wrote phase events to standard error.
They did not use `EUID_PROVE_TIMING_FILE`.
The timing-disabled samples measured instrumentation overhead.

## Desktop results

| Mode | Samples | Median prove | Median verify | Median peak RSS |
| --- | ---: | ---: | ---: | ---: |
| Timing enabled | 7 | 1,387 ms | 39 ms | 2,069.56 MiB |
| Timing disabled | 7 | 1,368 ms | 40 ms | 2,071.12 MiB |

The observed timing overhead was 19 ms, or 1.39%.
The complete cold sample order is in `desktop-cold.csv`.
The complete processes used about 5.7 CPU equivalents on average.
Rayon still had 12 workers; serial phases and synchronization reduce average CPU use.

One process ran six timing-enabled iterations.
The phase report discards the first iteration and uses the next five iterations as warm samples.
The warm `sdk/total` median was 1,235.679 ms.
The benchmark-reported verify median was 20 ms.
The six-iteration process peak RSS was 3,029.94 MiB.
This RSS value is the maximum for the complete process, not one warm proof.

A second six-iteration process disabled timing.
It reported a 1,339 ms prove median and an 18 ms verify median.
Its process peak RSS was 2,787.62 MiB.
The benchmark median includes all six iterations.
The seven counter-ordered cold pairs are the better instrumentation-overhead comparison.

## Phase medians

| Phase | Cold median | Warm median |
| --- | ---: | ---: |
| Public input preparation | 0.029 ms | 0.031 ms |
| Credential extraction | 0.685 ms | 0.718 ms |
| Witness generation | 191.302 ms | 179.229 ms |
| AIR core total | 1,193.658 ms | 1,055.948 ms |
| Tree 0 write and commit | 29.956 ms | 24.467 ms |
| Tree 1 write and commit | 155.315 ms | 128.599 ms |
| Tree 2 write and commit | 428.994 ms | 386.908 ms |
| Post-interaction GKR | 185.031 ms | 166.328 ms |
| STARK prove total | 381.069 ms | 357.779 ms |
| Envelope encoding | 0.503 ms | 0.492 ms |
| SDK total | 1,387.009 ms | 1,235.679 ms |

`composition_polynomial_generation` is inside `composition`.
The values in `desktop-phases.csv` must not add both phases.

The canonical wrapper outside `core_prove` used about 0.56 ms.
Credential extraction and witness generation explain almost all of the 192.80 ms gap between `sdk/core_prove` and `air_core/total`.
The AIR core used 86.1% of the cold end-to-end time.
The old campaign estimate that half of the path was outside the proof core does not apply to this circuit and entrypoint.

## Current circuit geometry

The circuit has 23,796,432 M31 cells across preprocessing, trace, interaction, and post-interaction columns.

| Module | Cells | Share |
| --- | ---: | ---: |
| Shared Keccak service | 12,460,800 | 52.4% |
| Private MSO SHA-256 | 4,685,824 | 19.7% |
| Private device ML-DSA | 3,671,616 | 15.4% |
| All other modules | 2,978,192 | 12.5% |

The phase data shows that tree 2 trace construction is the largest measured single phase.
The STARK composition work, post-interaction GKR, and tree 1 commitment are the next large costs.

## Limits

- A cold sample means a fresh process. It does not flush the operating-system file cache.
- Seven desktop samples define a useful local baseline. They do not define a broad hardware performance distribution.
