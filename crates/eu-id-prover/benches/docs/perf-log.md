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
| 2026-07-02 | a1224ae7 | WO-S1 `xor_8` GKR spike (blocked on MLE tie-back Q-003) | BM_ShaZK_equiv/1/prove (1-thread) | 1.0652 s | 1.0478 s |
| 2026-07-02 | a1224ae7 | WO-S1 `xor_8` GKR spike (blocked on MLE tie-back Q-003) | BM_ShaZK_equiv/1/verify | 612.77 µs | 764.98 µs |
| 2026-07-02 | a1224ae7 | WO-S1 `xor_8` GKR spike (blocked on MLE tie-back Q-003) | shape_dump total cells | 28,488,480 | 28,222,240 |
| 2026-07-02 | a1224ae7 | WO-S1 `xor_8` GKR spike (blocked on MLE tie-back Q-003) | shape_dump sha256 interaction cells | 5,800,640 | 5,534,400 |
| 2026-07-02 | a1224ae7 | WO-S1 `xor_8` GKR spike (blocked on MLE tie-back Q-003) | standalone SHA proof bytes | 60,045 | 73,749 |
| 2026-07-02 | a1224ae7 | WO-S1 `xor_8` GKR spike (blocked on MLE tie-back Q-003) | `xor_8` GKR wire proof bytes | 0 | 18,824 |
| 2026-07-03 | 6b3273e0 | WO-1.4 SIMD trace writers | hinted_mul schedule writer timing (default Rayon, ignored test) | 192.584 µs | 82.5 µs |
| 2026-07-03 | 6b3273e0 | WO-1.4 SIMD trace writers | hinted_mul base writer timing (default Rayon, ignored test) | 23.062542 ms | 3.015083 ms |
| 2026-07-03 | 6b3273e0 | WO-1.4 SIMD trace writers | SHA trace writer timing (default Rayon, ignored test) | 4.628708 ms | 868.75 µs |
| 2026-07-03 | 6b3273e0 | WO-1.4 SIMD trace writers | BM_ECDSAZKProver_equiv/1 (1-thread) | 1.894 s | 1.9128 s |
| 2026-07-03 | 6b3273e0 | WO-1.4 SIMD trace writers | BM_ShaZK_equiv/1/prove (1-thread) | 1.055 s | 1.0529 s |
| 2026-07-03 | 6b3273e0 | WO-1.4 SIMD trace writers | BM_ShaZK_equiv/33/prove (1-thread) | 1.154 s | 1.1421 s |
| 2026-07-03 | 6b3273e0 | WO-1.4 SIMD trace writers | pipeline/prove (parallel) | 690 ms | 663.79 ms |
| 2026-07-03 | 6b3273e0 | WO-1.4 SIMD trace writers | shape_dump total cells | 28,488,480 | 28,488,480 |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | BM_ShaZK_equiv/1/prove (1-thread) | — | 1.1069 s |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | BM_ShaZK_equiv/1/verify (1-thread) | — | 637.73 µs |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | BM_ShaZK_equiv/2/prove (1-thread) | — | 1.1167 s |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | BM_ShaZK_equiv/2/verify (1-thread) | — | 633.44 µs |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | BM_ShaZK_equiv/4/prove (1-thread) | — | 1.0756 s |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | BM_ShaZK_equiv/4/verify (1-thread) | — | 618.73 µs |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | BM_ShaZK_equiv/8/prove (1-thread) | — | 1.1134 s |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | BM_ShaZK_equiv/8/verify (1-thread) | — | 641.06 µs |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | BM_ShaZK_equiv/16/prove (1-thread) | — | 1.1664 s |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | BM_ShaZK_equiv/16/verify (1-thread) | — | 645.96 µs |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | BM_ShaZK_equiv/32/prove (1-thread) | — | 1.2097 s |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | BM_ShaZK_equiv/32/verify (1-thread) | — | 635.06 µs |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | BM_ShaZK_equiv/33/prove (1-thread) | — | 1.1994 s |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | BM_ShaZK_equiv/33/verify (1-thread) | — | 635.27 µs |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | BM_ECDSAZKProver_equiv/1 (1-thread) | — | 1.8981 s |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | BM_ECDSAZKVerifier_equiv/1 (1-thread) | — | 14.393 ms |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | BM_ECDSAZKProver_equiv/2 (1-thread) | — | 3.7211 s |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | BM_ECDSAZKVerifier_equiv/2 (1-thread; known 2-sig verifier bug did not fire in this run) | — | 28.901 ms |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | BM_ECDSAZKProver_equiv/3 (1-thread) | — | 5.6217 s |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | BM_ECDSAZKVerifier_equiv/3 (1-thread) | — | 43.239 ms |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | sha/prove (parallel identity_bench) | — | 276.33 ms |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | p256/prove (parallel identity_bench) | — | 404.57 ms |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | age/prove (parallel identity_bench) | — | 9.4577 ms |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | nat/prove (parallel identity_bench) | — | 2.0385 ms |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | pipeline/prove (parallel identity_bench) | — | 652.95 ms |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | combined proof bincode bytes | 1,601,906 | 2,318,946 |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | sha standalone STARK proof bytes | — | 60,045 |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | shape_dump p256 cells | — | 14,573,616 |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | shape_dump sha256 cells | — | 13,843,104 |
| 2026-07-03 | d27d9bb1 | WO-0 128-bit baseline | shape_dump total cells | — | 28,488,480 |
| 2026-07-03 | 49979dc7 | WO-2.5 signed-carry provider dedup | BM_ECDSAZKProver_equiv/1 (1-thread) | 1.8981 s | 1.8923 s |
| 2026-07-03 | 49979dc7 | WO-2.5 signed-carry provider dedup | pipeline/prove (parallel identity_bench) | 652.95 ms | 647.99 ms |
| 2026-07-03 | 49979dc7 | WO-2.5 signed-carry provider dedup | shape_dump p256 cells | 14,573,616 | 13,262,896 |
| 2026-07-03 | 49979dc7 | WO-2.5 signed-carry provider dedup | shape_dump total cells | 28,488,480 | 27,177,760 |
| 2026-07-03 | b4183edc | WO-3.5 hand-CSE hot evals | proof bytes equality (`valid_over_18`) | 2,321,174 / `cfbb3996…09eb2ac` | identical |
| 2026-07-03 | b4183edc | WO-3.5 hand-CSE hot evals | BM_ECDSAZKProver_equiv/1 (1-thread) | 1.8923 s | 1.8129 s |
| 2026-07-03 | b4183edc | WO-3.5 hand-CSE hot evals | BM_ShaZK_equiv/33/prove (1-thread) | 1.1994 s | 1.1966 s |
| 2026-07-03 | b4183edc | WO-3.5 hand-CSE hot evals | composition-span timing | no local harness found | not measured (Q-011) |
| 2026-07-03 | 85feb27c | WO-1.6 prove twiddle cache | repeated prove timing (same witness) | first 814.184 ms | second 826.154 ms |
| 2026-07-03 | 85feb27c | WO-1.6 prove twiddle cache | repeated proof bytes | — | identical |
| 2026-07-03 | 85feb27c | WO-1.6 prove twiddle cache | BM_ECDSAZKProver_equiv/1 cold path (1-thread) | 1.8129 s | 1.8059 s |

WO-1.8 note: `target-cpu=native` was measured with `RUSTFLAGS="-C target-cpu=native"` instead of committed `.cargo/config.toml`, because CI builds this repo on `ubuntu-latest` and would consume committed Cargo config. LTO/CU1 is scoped to `[profile.bench]`; putting it in `[profile.release]` made `cargo test --workspace --release` fail in the P-256 monolithic proof gate with `ProofLayer("Constraints not satisfied.")`.

WO-1.4 note: P-256 trace writers use the scalar path when `RAYON_NUM_THREADS=1`, because direct packed/rayon generation is faster only with a multi-thread Rayon pool. The single-thread ECDSA prover result is therefore noise-level unchanged; the measurable accepted movement is SHA/33 and the parallel pipeline.

WO-0 note: `wo30-128bit` fast-forwarded to `d27d9bb1`, setting the combined P-256 profile to `pow_bits = 10` and `n_queries = 59` for the signed-off 128-bit target. Benchmarks were run under `tasks/parity/BENCH-LOCK`; combined proof bytes came from `eu-id prove --fixture valid_over_18`.

WO-2.5 note: public-key-curve and final-add now share one projective signed-carry provider relation/table; scalar-setup remains separate because it uses a different equation. The WO predicted a ~1.83M-cell drop by counting value/active preprocessed columns, but those IDs were already globally deduped at WO-0, so the measured reduction is 1,310,720 cells: one duplicate provider's base multiplicity column plus four interaction columns at log 18.

WO-3.5 note: hand-CSE touched `hinted_mul`, scalar-mod-mul `Ab`/`Qn`, and SHA main-round evals only; proof bytes for `valid_over_18` were byte-identical before/after. Searches under `crates/` found no tracing subscriber/harness for the requested `CompositionPolynomialGeneration` span, so Q-011 asks whether to add one as follow-up.

WO-1.6 note: only the twiddle cache was implemented. The repeated-prove byte equality guard passed, but the second prove was slower in two diagnostics (`818.426ms → 856.221ms`, then `814.184ms → 826.154ms`), so Q-012 asks whether to stop here or pursue broader preprocessed-column caches.
