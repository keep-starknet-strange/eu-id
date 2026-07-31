# TS13 `pq_perf_probe` benchmark

Date: 2026-07-30

This report records one `pq_perf_probe` benchmark at the source commit below.
It does not measure the canonical identity proof.
Do not compare its proof size with the canonical envelope size.

## Provenance

- Commit: `088df06491f466b8d481f7d9911681c8834edf22`
- Host: Apple M2 Max (`Mac14,5`)
- Memory: 32 GiB
- CPU: 12 physical cores and 12 logical cores
- Operating system: macOS 26.5.2, arm64
- Rust: `rustc 1.94.0-nightly (86a49fd71 2026-01-14)`
- Stwo revision:
  `4f39939eacd0c5efc8ee157e4215a250ca29168f`
- Rayon threads: 12
- Build profile: release, fat LTO, one code-generation unit
- Cargo features: default features
- Probe: `eu-id-prover/examples/pq_perf_probe.rs`
- Fixture: `mldsa_realistic_pid_fixture_with_age_over_18`
- Iterations: one iteration in each fresh process

The fixture used ML-DSA-65 for all three signatures.
The signatures authenticated the issuer, device, and revocation data.
The fixture requested `age_over_18 = true`.
The verifier rebuilt the canonical tree-zero root for each run.

The measured PCS configuration was:

```text
PcsConfig {
    pow_bits: 20,
    fri_config: FriConfig::new(1, 3, 36, 2),
    lifting_log_size: None,
}
```

## Results

| Run | Prove | Verify | Tree zero | STARK verify | Raw proof | Bzip2 proof | Peak RSS |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1R | 759 ms | 41 ms | 22 ms | 18 ms | 1,557,635 bytes | 1,217,883 bytes | 969,900,032 bytes |
| 2 | 756 ms | 44 ms | 25 ms | 18 ms | 1,556,499 bytes | 1,218,296 bytes | 967,180,288 bytes |
| 3 | 749 ms | 48 ms | 28 ms | 19 ms | 1,556,307 bytes | 1,216,920 bytes | 969,048,064 bytes |
| **Median** | **756 ms** | **44 ms** | **25 ms** | **18 ms** | **1,556,499 bytes** | **1,217,883 bytes** | **969,048,064 bytes** |

The excluded first run did not report peak resident memory.
The replacement run is Run 1R.

The probe reported:

```text
zero_knowledge=false
scope=in_process_core
```

These values show that this report is not acceptance evidence for the
canonical proof.
