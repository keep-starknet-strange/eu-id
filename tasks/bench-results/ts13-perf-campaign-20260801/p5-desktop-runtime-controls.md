# P5 desktop runtime-control checkpoint

Status: preliminary. P2 will change the circuit. Run the final device sweep after P2.

## Input

- Source commit: `5a6087767726a5fffe5c67d3781aa8429318d21f`
- Circuit hash: `cc4c00d4fa753641afb2a9a3b08635f8a7ee35bd1bccb708e0d0dd8a8619b729`
- Proof body capacity: 1,572,864 bytes
- Identity-proof envelope: 1,572,910 bytes
- Binary SHA-256: `eed0b4f39a5ff5f319abafc78b14668e8bc8571611615b734aa734ae3ac78b1a`
- Host: MacBook Pro, Apple M2 Max, 8 performance cores and 4 efficiency cores, 32 GB RAM
- OS: macOS 26.5.2, arm64
- Rust: 1.94.0-nightly (`86a49fd71fecd25b0fd20247db0ba95eeceaba28`)
- Build: Cargo release profile, `-j12`
- Stack: 64 MiB for the proof thread and each Rayon worker
- Sample: one cold proof in each fresh process

## Worker sweep

The 4-worker and 6-worker points use three samples. The 8-worker and 12-worker points use seven
counterordered samples. Each value is the median.

| Requested workers | Reported workers | Prove | Verify | Witness | AIR core |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 4 | 4 | 1,430 ms | 54 ms | 83.168 ms | 1,346.180 ms |
| 6 | 6 | 1,222 ms | 48 ms | 74.713 ms | 1,143.901 ms |
| 8 | 8 | 1,120 ms | 43 ms | 74.745 ms | 1,043.009 ms |
| 12 | 12 | 1,139 ms | 44 ms | 74.956 ms | 1,062.252 ms |

The 8-worker median is 1.7% lower than the 12-worker median. The samples contain scheduler noise.
This result does not select the mobile worker count.

## Memory

macOS does not provide `/proc/self/status`. The phase records therefore contain null RSS and HWM
values. Two extra fresh processes used `/usr/bin/time -l`.

| Workers | Prove | Maximum resident set | Peak memory footprint |
| ---: | ---: | ---: | ---: |
| 8 | 1,286 ms | 1,981,825,024 bytes | 1,903,069,344 bytes |
| 12 | 1,083 ms | 1,992,081,408 bytes | 1,917,471,072 bytes |

The two memory samples differ by less than 1%. P2 must provide the main memory reduction. The final
Firebase sweep must select the worker count and affinity policy on the binding phones.
