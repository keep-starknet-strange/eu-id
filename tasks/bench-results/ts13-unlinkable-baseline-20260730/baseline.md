# TS13 unlinkability pre-profile baseline — 2026-07-30

## Result

The matched three-process baseline is:

| Metric | Median of Run 1R, Run 2, Run 3 |
| --- | ---: |
| Internal prove | 756 ms |
| Forced-fresh verify | 44 ms |
| Fresh tree-zero root | 25 ms |
| STARK verification | 18 ms |
| Raw proof | 1,556,499 bytes |
| Bzip2 wire proof | 1,217,883 bytes |
| Bzip2 compression | 103 ms |
| Bzip2 decompression | 50 ms |
| External elapsed time | 0.97 s |
| Peak RSS | 969,048,064 bytes (924.15625 MiB) |

This is a frozen pre-profile measurement of the merged Phase-1 implementation. The probe reports
`zero_knowledge=false` and `scope=in_process_core`; these results are not evidence that the later
unlinkable V4 protocol is implemented.

## Provenance

- Repository: `/Users/lucas/eu-id/.codex/worktrees/ts13-unlinkable-v1`
- Branch: `codex/ts13-unlinkable-v1`
- Commit: `088df06491f466b8d481f7d9911681c8834edf22`
- Measured at: `2026-07-30 12:12:37 CEST (+0200)` / `2026-07-30 10:12:37 UTC`
- Code provenance: `crates/`, `Cargo.toml`, and `Cargo.lock` had no working-tree changes.
  An unrelated modification to `tasks/todo.md` and an untracked
  `docs/ts13-unlinkable-age18-demo-spec.md` existed and were not part of the binary.
- Binary:
  `/private/tmp/ts13-unlinkable-baseline-target.pzZVzL/release/examples/pq_perf_probe`
- Binary SHA-256:
  `163ef464fd0dc9f613db9127ed7d79f40c6adb4c438a77e73c03db5368068f73`

The release binary was built once in a unique target directory:

```text
rtk proxy env CARGO_TARGET_DIR=/private/tmp/ts13-unlinkable-baseline-target.pzZVzL \
  rtk cargo build --release -p eu-id-prover --example pq_perf_probe
```

The workspace release profile used fat LTO and one codegen unit. No Cargo feature flags were passed,
so `eu-id-prover` optional features, including `unlink-spikes`, were disabled. Stwo's parallel path
was nevertheless enabled by dependency feature unification through
`stwo-constraint-framework`'s `parallel` feature. Every measured process explicitly set
`RAYON_NUM_THREADS=12`, and every probe output independently reported `rayon_threads=12`.

## Fixture and proof configuration

- Probe: `eu-id-prover/examples/pq_perf_probe.rs`, one iteration per fresh process.
- Fixture: deterministic `mldsa_realistic_pid_fixture_with_age_over_18`.
- Credential shape: seven PID attributes with 32-byte item randoms; only `age_over_18 = true` was
  requested through `ValueEquality([0xf5])`.
- Algorithms exercised: ML-DSA-65 issuer, ML-DSA-65 device authentication, and ML-DSA-65
  revocation signature.
- Session input: `openid4vp_session_transcript(b"session-transcript-123")`.
- Device authentication profile: `Iso180135`.
- Policy: current date `2026-07-03`, minimum age 18, accepted nationalities 276 and 250.
- Revocation: MSO-derived identifier, epoch 7, strict lower/upper bounds around the identifier.
- Stable input shape reported by every process:
  `PQ_ATTRIBUTE_LOADS [["age_over_18",100,2]]`; revocation SHA-256 used 2,560 rows / 40 blocks.
- Stwo revision:
  `4f39939eacd0c5efc8ee157e4215a250ca29168f`.
- Production PCS:
  `PcsConfig { pow_bits: 20, fri_config: FriConfig::new(1, 3, 36, 2), lifting_log_size: None }`.
- Verification path: `verify_mdoc_circuit_with_pcs_config_profiled_fresh`, requiring a fresh
  canonical tree-zero root rather than a cache hit.

## Environment

- Hardware: Apple M2 Max (`Mac14,5`)
- Memory: 34,359,738,368 bytes (32 GiB)
- CPU counts: 12 physical, 12 logical
- CPU affinity: not pinned
- OS: macOS 26.5.2, build 25F84; Darwin 25.5.0; arm64
- Rust:
  `rustc 1.94.0-nightly (86a49fd71 2026-01-14)`,
  host `aarch64-apple-darwin`, LLVM 21.1.8
- Cargo: `cargo 1.94.0-nightly (6d1bd93c4 2026-01-10)`
- Rayon threads: 12

## Process accounting

Four proof processes executed in total.

The original Run 1 completed successfully and emitted all probe metrics. The sandbox then denied
the `/usr/bin/time -l` wrapper's `sysctl kern.clockrate` read, causing the wrapper to exit 1 without
printing peak RSS. Run 1 is preserved below but excluded from the matched summary. After explicit
coordinator authorization, Run 1R replaced it under the same command with the timing wrapper's
read permission enabled. The matched summary is therefore exactly Run 1R, Run 2, and Run 3.

Each invocation was:

```text
rtk proxy env RAYON_NUM_THREADS=12 /usr/bin/time -l \
  /private/tmp/ts13-unlinkable-baseline-target.pzZVzL/release/examples/pq_perf_probe \
  --iterations 1
```

On this macOS host, `/usr/bin/time -l` reported maximum resident set size in bytes.

## Per-process results

| Run | Summary set | Prove ms | Verify ms | Tree 0 ms | STARK verify ms | Raw bytes | Bzip2 bytes | Compress ms | Decompress ms | Real s | User s | Sys s | Peak RSS bytes |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | Excluded: RSS instrumentation failure | 782 | 44 | 25 | 18 | 1,555,619 | 1,215,769 | 105 | 51 | 1.38 | 4.22 | 0.93 | unavailable |
| 1R | Included | 759 | 41 | 22 | 18 | 1,557,635 | 1,217,883 | 103 | 50 | 0.97 | 4.17 | 0.91 | 969,900,032 |
| 2 | Included | 756 | 44 | 25 | 18 | 1,556,499 | 1,218,296 | 102 | 49 | 0.97 | 4.07 | 0.87 | 967,180,288 |
| 3 | Included | 749 | 48 | 28 | 19 | 1,556,307 | 1,216,920 | 104 | 52 | 0.97 | 3.92 | 0.91 | 969,048,064 |
| **Median, 1R/2/3** | **Matched baseline** | **756** | **44** | **25** | **18** | **1,556,499** | **1,217,883** | **103** | **50** | **0.97** | **4.07** | **0.91** | **969,048,064** |

The median detailed raw-proof breakdown over Run 1R, Run 2, and Run 3 is:

```json
{
  "proof_bytes": 1556499,
  "stark_proof_bytes": 1536397,
  "outer_proof_bytes": 20102,
  "post_interaction_payload_bytes": 16872,
  "stark": {
    "config": 25,
    "commitments": 168,
    "sampled_values": 225968,
    "decommitments": 68368,
    "queried_values": 1189296,
    "proof_of_work": 8,
    "fri_proof": 52564
  }
}
```

## Raw outputs

### Run 1 — original, excluded from matched summary

```text
1.38 real         4.22 user         0.93 sys
time: sysctl kern.clockrate: Operation not permitted
PQ_ATTRIBUTE_LOADS [["age_over_18",100,2]]
PQ_PERF_PROBE zero_knowledge=false scope=in_process_core iterations=1 rayon_threads=12 phase1_prove_ms=782 phase1_verify_ms=44 phase1_proof_bytes=1555619 phase1_revocation_sha_rows=2560 phase1_revocation_sha_blocks=40 fresh_tree0_root_median_ms=25 fresh_stark_verify_median_ms=18 bzip2_compress_median_ms=105 bzip2_decompress_median_ms=51 bzip2_wire_median_bytes=1215769
{"proof_bytes":1555619,"stark_proof_bytes":1535517,"outer_proof_bytes":20102,"post_interaction_payload_bytes":16872,"stark":{"config":25,"commitments":168,"sampled_values":225968,"decommitments":67728,"queried_values":1189296,"proof_of_work":8,"fri_proof":52324}}
```

### Run 1R — replacement, included

```text
0.97 real         4.17 user         0.91 sys
969900032 maximum resident set size
PQ_ATTRIBUTE_LOADS [["age_over_18",100,2]]
PQ_PERF_PROBE zero_knowledge=false scope=in_process_core iterations=1 rayon_threads=12 phase1_prove_ms=759 phase1_verify_ms=41 phase1_proof_bytes=1557635 phase1_revocation_sha_rows=2560 phase1_revocation_sha_blocks=40 fresh_tree0_root_median_ms=22 fresh_stark_verify_median_ms=18 bzip2_compress_median_ms=103 bzip2_decompress_median_ms=50 bzip2_wire_median_bytes=1217883
{"proof_bytes":1557635,"stark_proof_bytes":1537533,"outer_proof_bytes":20102,"post_interaction_payload_bytes":16872,"stark":{"config":25,"commitments":168,"sampled_values":225968,"decommitments":68688,"queried_values":1189296,"proof_of_work":8,"fri_proof":53380}}
```

### Run 2 — included

```text
0.97 real         4.07 user         0.87 sys
967180288 maximum resident set size
PQ_ATTRIBUTE_LOADS [["age_over_18",100,2]]
PQ_PERF_PROBE zero_knowledge=false scope=in_process_core iterations=1 rayon_threads=12 phase1_prove_ms=756 phase1_verify_ms=44 phase1_proof_bytes=1556499 phase1_revocation_sha_rows=2560 phase1_revocation_sha_blocks=40 fresh_tree0_root_median_ms=25 fresh_stark_verify_median_ms=18 bzip2_compress_median_ms=102 bzip2_decompress_median_ms=49 bzip2_wire_median_bytes=1218296
{"proof_bytes":1556499,"stark_proof_bytes":1536397,"outer_proof_bytes":20102,"post_interaction_payload_bytes":16872,"stark":{"config":25,"commitments":168,"sampled_values":225968,"decommitments":68368,"queried_values":1189296,"proof_of_work":8,"fri_proof":52564}}
```

### Run 3 — included

```text
0.97 real         3.92 user         0.91 sys
969048064 maximum resident set size
PQ_ATTRIBUTE_LOADS [["age_over_18",100,2]]
PQ_PERF_PROBE zero_knowledge=false scope=in_process_core iterations=1 rayon_threads=12 phase1_prove_ms=749 phase1_verify_ms=48 phase1_proof_bytes=1556307 phase1_revocation_sha_rows=2560 phase1_revocation_sha_blocks=40 fresh_tree0_root_median_ms=28 fresh_stark_verify_median_ms=19 bzip2_compress_median_ms=104 bzip2_decompress_median_ms=52 bzip2_wire_median_bytes=1216920
{"proof_bytes":1556307,"stark_proof_bytes":1536205,"outer_proof_bytes":20102,"post_interaction_payload_bytes":16872,"stark":{"config":25,"commitments":168,"sampled_values":225968,"decommitments":68208,"queried_values":1189296,"proof_of_work":8,"fri_proof":52532}}
```
