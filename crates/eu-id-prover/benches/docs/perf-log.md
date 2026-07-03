# Perf log — benches of record

Single-thread: `RAYON_NUM_THREADS=1 cargo bench -p eu-id-prover --bench longfellow_equiv_bench`
(the env var is mandatory — rayon is an unconditional stwo-p256 dep; baselines below predate this rule and were run without it)
Parallel: `cargo bench -p eu-id-prover --bench identity_bench --features parallel -- 'prove'`
Shape: `cargo test -p eu-id-prover --release shape_dump -- --ignored --nocapture`

| date | commit | change (WO) | bench | before | after |
|---|---|---|---|---|---|
| 2026-07-02 | 8cb0a461 | baseline | BM_ECDSAZKProver_equiv/1 (1-thread) | — | 565 ms |
| 2026-07-02 | 8cb0a461 | baseline | BM_ShaZK_equiv/1 (1-thread) | — | 331 ms |
| 2026-07-02 | 8cb0a461 | baseline | BM_ShaZK_equiv/33 (1-thread) | — | 383 ms |
| 2026-07-02 | 8cb0a461 | baseline | pipeline/prove (12-core parallel) | — | 820 ms |
| 2026-07-02 | 8cb0a461 | baseline | shape_dump total cells | — | 28,488,480 |
| 2026-07-02 | e72cc328 | WO-1.8 +bench LTO/CU1 | BM_ECDSAZKProver_equiv/1 (1-thread) | 2.258 s | 1.911 s |
| 2026-07-02 | e72cc328 | WO-1.8 +bench LTO/CU1 | BM_ShaZK_equiv/1 (1-thread) | 1.393 s | 1.161 s |
| 2026-07-02 | e72cc328 | WO-1.8 +bench LTO/CU1 | BM_ShaZK_equiv/33 (1-thread) | 1.525 s | 1.284 s |
| 2026-07-02 | e72cc328 | WO-1.8 +bench LTO/CU1 | pipeline/prove (parallel) | 933 ms | 771 ms |
| 2026-07-02 | e72cc328 | WO-1.8 +native via RUSTFLAGS | BM_ECDSAZKProver_equiv/1 (1-thread) | 1.911 s | 1.890 s |
| 2026-07-02 | e72cc328 | WO-1.8 +native via RUSTFLAGS | BM_ShaZK_equiv/1 (1-thread) | 1.161 s | 1.120 s |
| 2026-07-02 | e72cc328 | WO-1.8 +native via RUSTFLAGS | BM_ShaZK_equiv/33 (1-thread) | 1.284 s | 1.212 s |
| 2026-07-02 | e72cc328 | WO-1.8 +native via RUSTFLAGS | pipeline/prove (parallel) | 771 ms | 716 ms |
| 2026-07-02 | e72cc328 | WO-1.8 +bench mimalloc | BM_ECDSAZKProver_equiv/1 (1-thread) | 1.890 s | 1.894 s |
| 2026-07-02 | e72cc328 | WO-1.8 +bench mimalloc | BM_ShaZK_equiv/1 (1-thread) | 1.120 s | 1.055 s |
| 2026-07-02 | e72cc328 | WO-1.8 +bench mimalloc | BM_ShaZK_equiv/33 (1-thread) | 1.212 s | 1.154 s |
| 2026-07-02 | e72cc328 | WO-1.8 +bench mimalloc | pipeline/prove (parallel) | 716 ms | 700 ms |
| 2026-07-02 | 80dabe23 | WO-1.7 SHA coefficient retention | contended sha/prove soak | wedged 4x at sha/prove | 3 x 30 min clean: 41/48/46 iterations |
| 2026-07-02 | 80dabe23 | WO-1.7 exact parallel bench | identity_bench `--features parallel -- 'prove'` | wedge at sha/prove | passed; sha/prove 263 ms, pipeline/prove 690 ms |
| 2026-07-02 | 1f461ac8 | WO-1.1 hint/draft generation (RAYON_NUM_THREADS=1) | `hint_gen_timing` checked vs optimized median | 323.335 ms | 157.269 ms |
| 2026-07-02 | 1f461ac8 | WO-1.1 hint/draft generation (default Rayon) | `hint_gen_timing` checked vs optimized median | 192.371 ms | 58.347 ms |
| 2026-07-02 | 1f461ac8 | WO-1.1 blocked acceptance check (Q-002) | BM_ECDSAZKProver_equiv/1 (1-thread; draft prebuilt by harness) | 1.894 s | 1.874 s |
| 2026-07-02 | 81e946e9 | WO-S1 `xor_8` GKR spike (blocked on MLE tie-back Q-003) | BM_ShaZK_equiv/1/prove (1-thread) | 1.0652 s | 1.0478 s |
| 2026-07-02 | 81e946e9 | WO-S1 `xor_8` GKR spike (blocked on MLE tie-back Q-003) | BM_ShaZK_equiv/1/verify | 612.77 µs | 764.98 µs |
| 2026-07-02 | 81e946e9 | WO-S1 `xor_8` GKR spike (blocked on MLE tie-back Q-003) | shape_dump total cells | 28,488,480 | 28,222,240 |
| 2026-07-02 | 81e946e9 | WO-S1 `xor_8` GKR spike (blocked on MLE tie-back Q-003) | shape_dump sha256 interaction cells | 5,800,640 | 5,534,400 |
| 2026-07-02 | 81e946e9 | WO-S1 `xor_8` GKR spike (blocked on MLE tie-back Q-003) | standalone SHA proof bytes | 60,045 | 73,749 |
| 2026-07-02 | 81e946e9 | WO-S1 `xor_8` GKR spike (blocked on MLE tie-back Q-003) | `xor_8` GKR wire proof bytes | 0 | 18,824 |

WO-1.8 note: `target-cpu=native` was measured with `RUSTFLAGS="-C target-cpu=native"` instead of committed `.cargo/config.toml`, because CI builds this repo on `ubuntu-latest` and would consume committed Cargo config. LTO/CU1 is scoped to `[profile.bench]`; putting it in `[profile.release]` made `cargo test --workspace --release` fail in the P-256 monolithic proof gate with `ProofLayer("Constraints not satisfied.")`.
