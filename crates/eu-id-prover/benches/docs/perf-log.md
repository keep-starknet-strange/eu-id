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
| 2026-07-04 | worktree | WO-M5 shared mdoc SHA table provider (RAYON_NUM_THREADS=1, BENCH_ITERS=3) | mdoc_perf_probe prove | 2133 ms | 996 ms |
| 2026-07-04 | worktree | WO-M5 shared mdoc SHA table provider (RAYON_NUM_THREADS=1, BENCH_ITERS=3) | mdoc_perf_probe verify | 45 ms | 45 ms |
| 2026-07-04 | worktree | WO-M5 shared mdoc SHA table provider (RAYON_NUM_THREADS=1, BENCH_ITERS=3) | mdoc proof bytes | 1,809,542 | 1,759,326 |
| 2026-07-04 | worktree | WO-M5 shared mdoc SHA table provider | mdoc shape cells | 21,824,128 | 6,487,840 |
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
| 2026-07-03 | 237969dd | WO-1.1 close-out (Q-002) | identity_e2e/prove_identity (RAYON_NUM_THREADS=1; witness build inside loop) | bench absent before close-out | 2.6204 s |
| 2026-07-02 | a1224ae7 | WO-S1 `xor_8` GKR spike (blocked on MLE tie-back Q-003) | BM_ShaZK_equiv/1/prove (1-thread) | 1.0652 s | 1.0478 s |
| 2026-07-02 | a1224ae7 | WO-S1 `xor_8` GKR spike (blocked on MLE tie-back Q-003) | BM_ShaZK_equiv/1/verify | 612.77 µs | 764.98 µs |
| 2026-07-02 | a1224ae7 | WO-S1 `xor_8` GKR spike (blocked on MLE tie-back Q-003) | shape_dump total cells | 28,488,480 | 28,222,240 |
| 2026-07-02 | a1224ae7 | WO-S1 `xor_8` GKR spike (blocked on MLE tie-back Q-003) | shape_dump sha256 interaction cells | 5,800,640 | 5,534,400 |
| 2026-07-02 | a1224ae7 | WO-S1 `xor_8` GKR spike (blocked on MLE tie-back Q-003) | standalone SHA proof bytes | 60,045 | 73,749 |
| 2026-07-02 | a1224ae7 | WO-S1 `xor_8` GKR spike (blocked on MLE tie-back Q-003) | `xor_8` GKR wire proof bytes | 0 | 18,824 |
| 2026-07-03 | worktree | Item 3 Phase 1 `xor_8` GKR tie-back (RAYON_NUM_THREADS=1) | BM_ShaZK_equiv/1/prove | 1.0046 s | 1.2835 s |
| 2026-07-03 | worktree | Item 3 Phase 1 `xor_8` GKR tie-back (RAYON_NUM_THREADS=1) | BM_ShaZK_equiv/1/verify | 846.76 µs | 880.82 µs |
| 2026-07-03 | worktree | Item 3 Phase 1 `xor_8` GKR tie-back | shape_dump composed total cells | 37,500,240 | 37,238,096 |
| 2026-07-03 | worktree | Item 3 Phase 1 `xor_8` GKR tie-back | shape_dump sha256 interaction cells | 5,800,640 | 5,538,496 |
| 2026-07-03 | worktree | Item 3 Phase 1 `xor_8` GKR tie-back | sha standalone STARK proof bytes | 60,045 | 58,897 |
| 2026-07-03 | worktree | Item 3 Phase 1 `xor_8` GKR tie-back | `xor_8` GKR wire proof bytes | 0 | 9,992 |
| 2026-07-03 | worktree | Item 3 Phase 1 `xor_8` GKR tie-back | SHA STARK+GKR payload bytes | 60,045 | 68,889 |
| 2026-07-04 | worktree | Item 3 Phase 2 sigma-decode GKR tie-back (cumulative; RAYON_NUM_THREADS=1) | BM_ShaZK_equiv/1/prove | 1.0046 s | 1.3491 s |
| 2026-07-04 | worktree | Item 3 Phase 2 sigma-decode GKR tie-back (cumulative; RAYON_NUM_THREADS=1) | BM_ShaZK_equiv/1/verify | 846.76 µs | 1.1752 ms |
| 2026-07-04 | worktree | Item 3 Phase 2 sigma-decode GKR tie-back (cumulative) | shape_dump composed total cells | 37,500,240 | 37,238,096 |
| 2026-07-04 | worktree | Item 3 Phase 2 sigma-decode GKR tie-back (cumulative) | shape_dump sha256 interaction cells | 5,800,640 | 5,538,496 |
| 2026-07-04 | worktree | Item 3 Phase 2 sigma-decode GKR tie-back (cumulative) | sha standalone STARK proof bytes | 60,045 | 63,233 |
| 2026-07-04 | worktree | Item 3 Phase 2 sigma-decode GKR tie-back (cumulative) | `xor_8` GKR wire proof bytes | 0 | 9,992 |
| 2026-07-04 | worktree | Item 3 Phase 2 sigma-decode GKR tie-back (cumulative) | sigma-decode GKR wire proof bytes | 0 | 18,392 |
| 2026-07-04 | worktree | Item 3 Phase 2 sigma-decode GKR tie-back (cumulative) | SHA STARK+GKR payload bytes | 60,045 | 91,617 |
| 2026-07-04 | worktree | Item 3 Phase 2 split-pack GKR tie-back (cumulative; RAYON_NUM_THREADS=1) | BM_ShaZK_equiv/1/prove | 1.0046 s | 1.4686 s |
| 2026-07-04 | worktree | Item 3 Phase 2 split-pack GKR tie-back (cumulative; RAYON_NUM_THREADS=1) | BM_ShaZK_equiv/1/verify | 846.76 µs | 1.5943 ms |
| 2026-07-04 | worktree | Item 3 Phase 2 split-pack GKR tie-back (cumulative) | shape_dump composed total cells | 37,500,240 | 37,238,096 |
| 2026-07-04 | worktree | Item 3 Phase 2 split-pack GKR tie-back (cumulative) | shape_dump sha256 interaction cells | 5,800,640 | 5,538,496 |
| 2026-07-04 | worktree | Item 3 Phase 2 split-pack GKR tie-back (cumulative) | sha standalone STARK proof bytes | 60,045 | 63,713 |
| 2026-07-04 | worktree | Item 3 Phase 2 split-pack GKR tie-back (cumulative) | `xor_8` GKR wire proof bytes | 0 | 9,992 |
| 2026-07-04 | worktree | Item 3 Phase 2 split-pack GKR tie-back (cumulative) | sigma-decode GKR wire proof bytes | 0 | 18,392 |
| 2026-07-04 | worktree | Item 3 Phase 2 split-pack GKR tie-back (cumulative) | split-pack GKR wire proof bytes | 0 | 18,392 |
| 2026-07-04 | worktree | Item 3 Phase 2 split-pack GKR tie-back (cumulative) | SHA STARK+GKR payload bytes | 60,045 | 110,489 |
| 2026-07-04 | worktree | Item 3 Phase 2 `maj_ch` GKR tie-back (cumulative; RAYON_NUM_THREADS=1) | BM_ShaZK_equiv/1/prove | 1.0046 s | 1.6705 s |
| 2026-07-04 | worktree | Item 3 Phase 2 `maj_ch` GKR tie-back (cumulative; RAYON_NUM_THREADS=1) | BM_ShaZK_equiv/1/verify | 846.76 µs | 1.7869 ms |
| 2026-07-04 | worktree | Item 3 Phase 2 `maj_ch` GKR tie-back (cumulative) | shape_dump composed total cells | 37,500,240 | 37,238,096 |
| 2026-07-04 | worktree | Item 3 Phase 2 `maj_ch` GKR tie-back (cumulative) | shape_dump sha256 interaction cells | 5,800,640 | 5,538,496 |
| 2026-07-04 | worktree | Item 3 Phase 2 `maj_ch` GKR tie-back (cumulative) | sha standalone STARK proof bytes | 60,045 | 64,193 |
| 2026-07-04 | worktree | Item 3 Phase 2 `maj_ch` GKR tie-back (cumulative) | `xor_8` GKR wire proof bytes | 0 | 9,992 |
| 2026-07-04 | worktree | Item 3 Phase 2 `maj_ch` GKR tie-back (cumulative) | sigma-decode GKR wire proof bytes | 0 | 18,392 |
| 2026-07-04 | worktree | Item 3 Phase 2 `maj_ch` GKR tie-back (cumulative) | split-pack GKR wire proof bytes | 0 | 18,392 |
| 2026-07-04 | worktree | Item 3 Phase 2 `maj_ch` GKR tie-back (cumulative) | `maj_ch` GKR wire proof bytes | 0 | 13,872 |
| 2026-07-04 | worktree | Item 3 Phase 2 `maj_ch` GKR tie-back (cumulative) | SHA STARK+GKR payload bytes | 60,045 | 124,841 |
| 2026-07-04 | worktree | Item 3 Phase 2 decode/split/`maj_ch` actual conversion (cumulative; RAYON_NUM_THREADS=1) | BM_ShaZK_equiv/1/prove | 1.0046 s | 1.2735 s |
| 2026-07-04 | worktree | Item 3 Phase 2 decode/split/`maj_ch` actual conversion (cumulative; RAYON_NUM_THREADS=1) | BM_ShaZK_equiv/1/verify | 846.76 us | 1.7339 ms |
| 2026-07-04 | worktree | Item 3 Phase 2 decode/split/`maj_ch` actual conversion (cumulative) | shape_dump composed total cells | 37,500,240 | 31,995,216 |
| 2026-07-04 | worktree | Item 3 Phase 2 decode/split/`maj_ch` actual conversion (cumulative) | shape_dump sha256 interaction cells | 5,800,640 | 295,616 |
| 2026-07-04 | worktree | Item 3 Phase 2 decode/split/`maj_ch` actual conversion (cumulative) | sha standalone STARK proof bytes | 60,045 | 58,561 |
| 2026-07-04 | worktree | Item 3 Phase 2 decode/split/`maj_ch` actual conversion (cumulative) | `xor_8` GKR wire proof bytes | 0 | 9,992 |
| 2026-07-04 | worktree | Item 3 Phase 2 decode/split/`maj_ch` actual conversion (cumulative) | sigma-decode GKR wire proof bytes | 0 | 18,392 |
| 2026-07-04 | worktree | Item 3 Phase 2 decode/split/`maj_ch` actual conversion (cumulative) | split-pack GKR wire proof bytes | 0 | 18,392 |
| 2026-07-04 | worktree | Item 3 Phase 2 decode/split/`maj_ch` actual conversion (cumulative) | `maj_ch` GKR wire proof bytes | 0 | 13,872 |
| 2026-07-04 | worktree | Item 3 Phase 2 decode/split/`maj_ch` actual conversion (cumulative) | SHA STARK+GKR payload bytes | 60,045 | 119,209 |
| 2026-07-04 | worktree | Item 3 Phase 2 unified converted-SHA GKR batch (RAYON_NUM_THREADS=1) | BM_ShaZK_equiv/1/prove | 1.2735 s | 1.5040 s |
| 2026-07-04 | worktree | Item 3 Phase 2 unified converted-SHA GKR batch (RAYON_NUM_THREADS=1) | BM_ShaZK_equiv/1/verify | 1.7339 ms | 1.5584 ms |
| 2026-07-04 | worktree | Item 3 Phase 2 unified converted-SHA GKR batch | shape_dump composed total cells | 31,995,216 | 31,995,216 |
| 2026-07-04 | worktree | Item 3 Phase 2 unified converted-SHA GKR batch | shape_dump sha256 interaction cells | 295,616 | 295,616 |
| 2026-07-04 | worktree | Item 3 Phase 2 unified converted-SHA GKR batch | sha standalone STARK proof bytes | 58,561 | 57,489 |
| 2026-07-04 | worktree | Item 3 Phase 2 unified converted-SHA GKR batch | converted SHA GKR wire proof bytes | 60,648 | 34,272 |
| 2026-07-04 | worktree | Item 3 Phase 2 unified converted-SHA GKR batch | SHA STARK+GKR payload bytes | 119,209 | 91,761 |
| 2026-07-04 | worktree | Item 3 Phase 2 P-3 same-height log16 tie-back merge (RAYON_NUM_THREADS=1) | BM_ShaZK_equiv/1/prove | 1.5040 s | 1.2311 s |
| 2026-07-04 | worktree | Item 3 Phase 2 P-3 same-height log16 tie-back merge (RAYON_NUM_THREADS=1) | BM_ShaZK_equiv/1/verify | 1.5584 ms | 1.2466 ms |
| 2026-07-04 | worktree | Item 3 Phase 2 P-3 same-height log16 tie-back merge | shape_dump SHA post-interaction cols | 33 | 17 |
| 2026-07-04 | worktree | Item 3 Phase 2 P-3 same-height log16 tie-back merge | shape_dump SHA post-interaction cells | 4,194,304 | 3,145,728 |
| 2026-07-04 | worktree | Item 3 Phase 2 P-3 same-height log16 tie-back merge | shape_dump GRAND+POST cells | 36,189,520 | 35,140,944 |
| 2026-07-04 | worktree | Item 3 Phase 2 P-3 same-height log16 tie-back merge | sha standalone STARK proof bytes | 57,489 | 58,961 |
| 2026-07-04 | worktree | Item 3 Phase 2 P-3 same-height log16 tie-back merge | converted SHA GKR wire proof bytes | 34,272 | 34,272 |
| 2026-07-04 | worktree | Item 3 Phase 2 P-3 same-height log16 tie-back merge | SHA STARK+GKR payload bytes | 91,761 | 93,233 |
| 2026-07-04 | worktree | Item 3 Q-024 production GKR revert | sha standalone STARK proof bytes (`gkr-spike` shape dump) | 58,961 + 34,272 GKR wire | 60,045, no GKR wire |
| 2026-07-04 | worktree | Item 3 Q-024 production GKR revert | shape_dump sha256 interaction cells (`gkr-spike`) | 295,616 + 3,145,728 post cells | 5,800,640, no post tree |
| 2026-07-04 | worktree | Item 3 Q-024 production GKR revert | shape_dump composed cells (`gkr-spike`) | 35,140,944 GRAND+POST | 37,500,240 GRAND, no post tree |
| 2026-07-04 | worktree | Item 3 Q-024 production GKR revert (RAYON_NUM_THREADS=1, feature-off) | BM_ShaZK_equiv/1/prove | 1.2311 s | 993.73 ms |
| 2026-07-04 | worktree | Item 3 Q-024 production GKR revert (RAYON_NUM_THREADS=1, feature-off) | BM_ShaZK_equiv/1/verify | 1.2466 ms | 608.68 µs |
| 2026-07-04 | worktree | Item 3 Q-024/Q-026 disposition | production path | measured GKR net-negative | full LogUp tables; GKR kept as spike/upstream reopener only |
| 2026-07-04 | worktree | Item 3 predicate P-1 gate | age range-check table cells, removed vs tie-back | 13,936 removed | 18,816 tie-back; skip |
| 2026-07-04 | worktree | Item 3 predicate P-1 gate | age bit-decomposition table cells, removed vs tie-back | 13,056 removed | 17,408 tie-back; skip |
| 2026-07-04 | worktree | Item 3 predicate P-1 gate | nationality table cells, removed vs tie-back | 80 removed | 128 tie-back; skip |
| 2026-07-04 | worktree | Item 3 digest_bind P-1 gate | digest_bind range8 cells, removed vs tie-back | 1,280 removed | 2,048 tie-back; skip |
| 2026-07-04 | worktree | Item 3 digest_bind P-1 gate | digest_bind range13 cells, removed vs tie-back | 40,960 removed | 65,536 tie-back; skip |
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
| 2026-07-03 | 5686643b | WO-1.6 Q-012 static-generator probe | median measured static generator total (3x, RAYON_NUM_THREADS=1) | — | 43.812 ms |
| 2026-07-03 | 5686643b | WO-1.6 SHA preprocessed cache | repeated prove timing (same witness) | first 751.842 ms | second 697.826 ms |
| 2026-07-03 | 5686643b | WO-1.6 SHA preprocessed cache | repeated proof bytes | — | identical |
| 2026-07-03 | 5686643b | WO-1.6 SHA preprocessed cache | BM_ECDSAZKProver_equiv/1 cold path (1-thread, P256-only) | 1.7048 s | 1.6423 s |
| 2026-07-03 | b4a0752d | WO-1.11 witness-gen round 2 | `hint_gen_timing` optimized median (RAYON_NUM_THREADS=1, BENCH-LOCK) | 157.269 ms | 134.850 ms |
| 2026-07-03 | 8f4df6d7 | WO-3.2a shared range13 provider | BM_ECDSAZKProver_equiv/1 (1-thread) | 1.8059 s | 1.7761 s |
| 2026-07-03 | 8f4df6d7 | WO-3.2a shared range13 provider | shape_dump p256 cells | 13,262,896 | 13,099,056 |
| 2026-07-03 | 8f4df6d7 | WO-3.2a shared range13 provider | shape_dump total cells | 27,177,760 | 27,013,920 |
| 2026-07-03 | 8dbe5038 | WO-3.2b shared projective signed-carry provider | BM_ECDSAZKProver_equiv/1 (1-thread) | 1.7761 s | 1.7048 s |
| 2026-07-03 | 8dbe5038 | WO-3.2b shared projective signed-carry provider | shape_dump p256 cells | 13,099,056 | 11,788,336 |
| 2026-07-03 | 8dbe5038 | WO-3.2b shared projective signed-carry provider | shape_dump total cells | 27,013,920 | 25,703,200 |
| 2026-07-03 | 1755fd22 | WO-3.3 FRI sweep harness | current production config prove / verify (`pow=10, blowup=2, queries=59, last=5, fold=1`) | — | 3.031992 s / 20.866 ms |
| 2026-07-03 | 1755fd22 | WO-3.3 FRI sweep harness | recommended smallest-proof Pareto prove / verify (`pow=20, blowup=3, queries=36, last=5, fold=2`) | 3.031992 s / 20.866 ms | 4.194932 s / 17.844 ms |
| 2026-07-03 | 1755fd22 | WO-3.3 FRI sweep harness | proof bytes current → recommended | 2,302,954 | 1,482,322 |
| 2026-07-03 | 1755fd22 | WO-3.3 FRI sweep harness | `CompositionPolynomialGeneration` span current → recommended | 909.354 ms | 879.103 ms |
| 2026-07-03 | 205b6897 | WO-3.3 Q-015 FRI schedule confirmation (N=5) | prove time current → sanctioned candidate | 2.973136 s | 2.742077 s |
| 2026-07-03 | 205b6897 | WO-3.3 Q-015 FRI schedule confirmation (N=5) | verify time current → sanctioned candidate | 20.363 ms | 19.661 ms |
| 2026-07-03 | 205b6897 | WO-3.3 Q-015 FRI schedule confirmation (N=5) | proof bytes current → sanctioned candidate | 2,302,954 | 2,237,338 |
| 2026-07-03 | 1755fd22 | WO-3.1 blowup 2→1 eval | prove time (`pow=10,last=5,fold=1`, 128-bit) | blowup 2 / q59: 3.031992 s | blowup 1 / q118: 2.350327 s |
| 2026-07-03 | 1755fd22 | WO-3.1 blowup 2→1 eval | proof bytes (`pow=10,last=5,fold=1`, 128-bit) | blowup 2 / q59: 2,302,954 | blowup 1 / q118: 4,243,266 |
| 2026-07-03 | 1755fd22 | WO-3.1 blowup 2→1 eval | verify time (`pow=10,last=5,fold=1`, 128-bit) | blowup 2 / q59: 20.866 ms | blowup 1 / q118: 28.929 ms |
| 2026-07-03 | f1127b17 | WO-1.2 Stage 1 trace fan-out | proof bytes serial task path vs default fan-out | — | identical |
| 2026-07-03 | f1127b17 | WO-1.2 Stage 1 trace fan-out | BM_ECDSAZKProver_equiv/1 (RAYON_NUM_THREADS=1) | 1.7048 s | 2.1876 s median, Criterion no-change on rerun |
| 2026-07-03 | f1127b17 | WO-1.2 Stage 1 trace fan-out | pipeline/prove (default threads) | 647.99 ms | 533.90 ms |
| 2026-07-03 | worktree | mdoc Phase 0 baseline | mdoc/prove (RAYON_NUM_THREADS=1) | bench absent | 5.0325 s |
| 2026-07-03 | worktree | mdoc Phase 0 baseline | mdoc/verify (RAYON_NUM_THREADS=1) | bench absent | 28.089 ms |
| 2026-07-03 | worktree | mdoc Phase 0 baseline | mdoc proof bincode bytes | bench absent | 4,563,243 |
| 2026-07-03 | worktree | mdoc Phase 0 baseline | mdoc shape_dump total cells | shape absent | 79,988,576 |
| 2026-07-03 | worktree | mdoc Phase 0b guard + accepted sizing waste | mdoc/prove (RAYON_NUM_THREADS=1) | 5.0325 s | 5.0498 s, Criterion no-change |
| 2026-07-03 | worktree | mdoc Phase 0b guard + accepted sizing waste | mdoc/verify (RAYON_NUM_THREADS=1) | 28.089 ms | 27.798 ms, Criterion no-change |
| 2026-07-03 | worktree | mdoc Phase 0b guard + accepted sizing waste | mdoc proof bincode bytes | 4,563,243 | 4,563,243 |
| 2026-07-03 | worktree | mdoc Phase 0b accepted SHA/P256 waste | accepted waste cells | known waste unpriced | 529,792 |

WO-1.8 note: `target-cpu=native` was measured with `RUSTFLAGS="-C target-cpu=native"` instead of committed `.cargo/config.toml`, because CI builds this repo on `ubuntu-latest` and would consume committed Cargo config. LTO/CU1 is scoped to `[profile.bench]`; putting it in `[profile.release]` made `cargo test --workspace --release` fail in the P-256 monolithic proof gate with `ProofLayer("Constraints not satisfied.")`.

WO-1.4 note: P-256 trace writers use the scalar path when `RAYON_NUM_THREADS=1`, because direct packed/rayon generation is faster only with a multi-thread Rayon pool. The single-thread ECDSA prover result is therefore noise-level unchanged; the measurable accepted movement is SHA/33 and the parallel pipeline.

WO-1.1 close-out note: Q-002 accepted `hint_gen_timing` as the WO metric because `BM_ECDSAZKProver_equiv/*` intentionally prebuilds the draft. The added `identity_e2e/prove_identity` benchmark times the relying-party path with witness build inside the measured loop; no pre-WO-1.1 value exists for that bench group in-tree, so the row records the current product metric and the accepted hint-gen before/after rows above remain the WO speedup evidence.

WO-0 note: `wo30-128bit` fast-forwarded to `d27d9bb1`, setting the combined P-256 profile to `pow_bits = 10` and `n_queries = 59` for the signed-off 128-bit target. Benchmarks were run under `tasks/parity/BENCH-LOCK`; combined proof bytes came from `eu-id prove --fixture valid_over_18`.

WO-2.5 note: public-key-curve and final-add now share one projective signed-carry provider relation/table; scalar-setup remains separate because it uses a different equation. The WO predicted a ~1.83M-cell drop by counting value/active preprocessed columns, but those IDs were already globally deduped at WO-0, so the measured reduction is 1,310,720 cells: one duplicate provider's base multiplicity column plus four interaction columns at log 18.

WO-3.5 note: hand-CSE touched `hinted_mul`, scalar-mod-mul `Ab`/`Qn`, and SHA main-round evals only; proof bytes for `valid_over_18` were byte-identical before/after. Searches under `crates/` found no tracing subscriber/harness for the requested `CompositionPolynomialGeneration` span, so Q-011 asks whether to add one as follow-up.

WO-1.6 note: only the twiddle cache was implemented. The repeated-prove byte equality guard passed, but the second prove was slower in two diagnostics (`818.426ms → 856.221ms`, then `814.184ms → 826.154ms`), so Q-012 asks whether to stop here or pursue broader preprocessed-column caches.

WO-1.6 Q-012 note: temporary probe instrumentation measured exactly the specified static generators inside three full 1-thread identity proofs. Median total was 43.812 ms: selector tables 0.000 ms, deterministic prepared-point limb tables 0.000 ms, scalar_mod_mul preprocessed 0.419 ms, SHA preprocessed 43.354 ms. Per Q-012 threshold/routing, only SHA preprocessed generation was above threshold, so `stwo-sha256::generate_preprocessed_trace` now caches immutable preprocessed traces by `(group_width, log_n_rows)`. Tree-0 commitment injection remains out of scope: the Stwo API still requires a fresh `TreeBuilder::commit(channel)` to own the tree and mix its root.

WO-1.11 note: final-check witness generation now reuses the prepared-table scalar-mul outputs in the optimized trusted draft path instead of recomputing `u·base` and `3R` checks. Temporary stage timing showed the top single-thread medians before the change were approximately `hinted_mul_from_projective_rcb` 48.2 ms, `projective_rcb_air_trace` 30.6 ms, `prepared_table` 24.3 ms, `final_check` 23.6 ms, and `projective_ec_trace` 20.2 ms. After the change, `final_check` was ~0.04 ms and the remaining top stages were `hinted_mul_from_projective_rcb` ~49.0 ms, `projective_rcb_air_trace` ~31.2 ms, `prepared_table` ~24.5 ms, and `projective_ec_trace` ~20.5 ms. The 30 ms target is not reachable with remaining single-thread witness orchestration alone; it needs WO-1.2 parallelism or an AIR/witness restructure.

WO-3.2a note: the five log-13 range13 provider relations were unified into one shared provider for scalar-setup/final-check, scalar-mod-mul, public-key-curve, hinted-mul, and final-add. The architect estimate was ~196k cells assuming four full provider copies; the measured reduction is 163,840 cells because the range13 preprocessed value column was already globally deduped, so each removed copy contributed one base multiplicity column plus four interaction columns at log 13. Criterion reported "No change in performance detected" for the 1-thread prover despite the median moving 1.8059s → 1.7761s.

WO-3.2b note: the hinted formula signed-carry provider premise passed because it already used `projective_rcb_signed_carry_claim()` / `PROJECTIVE_RCB_SIGNED_CARRY_EQUATION`, matching the projective signed-carry equation, bound, and log size. The merge shares the projective signed-carry provider across public-key-curve, final-add, and hinted formula consumers. The architect estimate was ~1.8M cells assuming a full duplicate provider including two preprocessed columns; those preprocessed IDs were already deduped, so the measured reduction is 1,310,720 cells: one base multiplicity column plus four interaction columns at log 18.

WO-3.3 note: `examples/fri_sweep.rs` is feature-gated behind `fri-sweep` and uses sweep-only explicit config prove/verify helpers; the production wrapper still computes `p256.pcs_config()` and no production profile change was committed. Release BENCH-LOCK command: `RAYON_NUM_THREADS=1 FRI_SWEEP_SAMPLES=1 cargo run -p eu-id-prover --release --example fri_sweep --features fri-sweep`. The `fold_step=2` probe verified, so both fold steps were included. The recommended row is the smallest-proof Pareto point, not a speed win: it reduces proof bytes by 820,632 (35.63%) but regresses prove time by 1.162940s versus current in the one-sample sweep.

WO-3.3 Q-015 note: architect rejected the smallest-proof row and sanctioned `pow=10, log_blowup=2, n_queries=59, log_last_layer=1, fold_step=2` conditional on an N=5 confirmation. Confirmation command under BENCH-LOCK: `RAYON_NUM_THREADS=1 FRI_SWEEP_SAMPLES=5 FRI_SWEEP_Q015_CONFIRM=1 cargo run -p eu-id-prover --release --example fri_sweep --features fri-sweep`. Candidate still won prove time and proof bytes, so production P256 profile now uses `FriConfig::new(1, 2, 59, 2)`.

WO-3.1 note: the fair blowup-1 comparison kept `pow_bits=10`, `log_last_layer=5`, and `fold_step=1`, requiring 118 queries for 128-bit security. Blowup 1 improved one-sample prove time by 22.48%, but proof bytes grew by 1,940,312 bytes (84.25%) and verify time grew by 38.63%. Q-016 confirms reject/no-change because the blowup-1 proof is 4.24 MB, above the interim mobile proof-size ceiling of 2.5 MB; a server/desktop fast profile is a future variant outside this queue.

WO-1.2 note: implemented Q-014 Stage 1 only. P256 and SHA expose Send-only column tasks for preprocessed/base trace preparation; `eu-id-prover` runs those tasks with `rayon::join` when the Rayon pool has more than one worker, then assembles the non-Send provers and appends/commits columns serially in the original module order. `RAYON_NUM_THREADS=1` is forced down the serial task path. The first single-thread bench after the change reported a regression, but the immediate rerun reported "No change in performance detected"; the recorded median was noisy/thermally high. The default-thread desktop path improved `pipeline/prove` by 17.607%. Interaction fan-out is intentionally descoped.

mdoc Phase 0 note: `mdoc_bench` runs the isolated EUID mdoc profile-v1 fixture through `prove_mdoc_circuit` / `verify_mdoc_circuit`; setup/extraction happens outside Criterion's measured loop. Command: `RAYON_NUM_THREADS=1 cargo bench -p eu-id-prover --bench mdoc_bench`. Shape command: `cargo test -p eu-id-prover --release shape_dump -- --ignored --nocapture`. The 12-module mdoc shape totals were: issuer P256 11,792,688 cells; issuer SHA 14,057,248; issuer bridge 54,160; device P256 11,792,688; device SHA 14,057,248; device bridge 54,160; birth-date SHA 14,081,824; birth-date digest bind 592; nationality SHA 14,079,776; nationality digest bind 592; age 17,312; nationality predicate 288; grand total 79,988,576 cells.

mdoc Phase 0b note: Q-001 accepted SHA option 1 + P256 option 1 after pricing the waste and adding a preprocessed-ID/content invariant guard in `air-core::prove`. Natural SHA logs for the fixture are issuer 9, device 7, birth-date 8, nationality 8; `shared_sha_log` is 9. The accepted SHA trace+interaction padding waste is 529,792 cells: issuer 0, device 216,960, birth-date 156,928, nationality 155,904. The P256 `mdoc/device` namespace currently prefixes only hinted-mul schedule IDs; content-identical namespaced preprocessed duplication is 0 cells. Combined accepted waste is below the 1,000,000-cell threshold, so SHA/P256 refactors are not Phase 0b gates.
| 2026-07-04 | s4-lite worktree (architect harness) | S4 coprocessor v1 vs AIR — first head-to-head | coprocessor prove (1-thread, N=5 median) | — | 6,752 ms |
| 2026-07-04 | s4-lite worktree (architect harness) | S4 coprocessor v1 | coprocessor verify | — | 405.7 ms |
| 2026-07-04 | s4-lite worktree (architect harness) | S4 coprocessor v1 | witness gen (native field) | — | 24.7 ms |
| 2026-07-04 | s4-lite worktree (architect harness) | S4 coprocessor v1 | bundle bytes | — | 2,469,504 |

S4 head-to-head note (architect, 2026-07-04): harness = scratchpad/coproc-bench (path-dep on s4-lite worktree, same signature construction as longfellow_equiv, release+fat-LTO+native, BENCH-LOCK held). CONTEXT FOR THE 6.75s: the G1 (field ≤25ns/mult) and G2 (sumcheck ≤20ms) gates were SKIPPED during the build sprint; the crate uses p256 expose-field constant-time arithmetic (G1 would have rejected it); Ligero row encoding is naive Lagrange at the enlarged Q-020 parameters (its own §4 warned 250-600ms even at 25ns). Treat 6.75s as ungated-v1, not the track's floor — but the ≤25ms budget claim is UNVERIFIED until the gates run.

| 2026-07-04 | feat/proof-reductions (working tree) | mdoc Phase 0b — budget confirmation (no functional change) | mdoc `prove_mdoc_circuit` (1-thread, release, N=5 median) | — | 1,797 ms |
| 2026-07-04 | feat/proof-reductions (working tree) | mdoc Phase 0b — budget confirmation | POC `prove_identity` monolith (1-thread, release, N=5 median) | — | 1,118 ms |
| 2026-07-04 | feat/proof-reductions (working tree) | mdoc Phase 0b — budget confirmation | mdoc / POC prove ratio (the ≤2.0× gate) | — | 1.61× |

mdoc Phase 0b budget-confirmation note (2026-07-04): the 5-6s vs 2.9s figure in the task premise was a cross-machine artifact; on a quiet box, same build/conditions, both proves are far lower and the RATIO is the gate. Measured medians (temp probe, 5 reps each, removed after): mdoc 1,797 ms (min 1,738), POC 1,118 ms (min 1,084) → **1.61× < 2.0× budget, PASS**. Diagnosis (measurement-first): the four SHA modules are ~70% of the 79.99M-cell circuit; the single largest cost is the per-instance SHA table-provider (multiplicity) columns — 19 components at log-16/18, **~7.47M cells per instance × 4 = ~29.9M cells (37% of the circuit)** — exactly Q-001's SHA option 3 (multi-message SHA module), which is out of scope. The three ranked fixes yield no net win, all confirmed by measurement: (a) per-instance SHA `log_n_rows` conflicts with tree-0 preprocessed dedup — the ~6.3M-cell σ/Σ/xor/split-pack tables are already deduped at fixed LOG_SIZE_16, and only 10 log-dependent columns (`is_first_row` + 9 round-cyclic) share a log-independent id whose content differs by log, so per-instance sizing trips `assert_preprocessed_id_content_invariant`; it would save 529,792 padding cells (0.66%) only by 4×-duplicating the 6.3M table set — a regression. Rejected. (b) table-provider consolidation is the real prize but requires a multi-message SHA witness surface that does not exist (blocks currently chain to one digest) — >1 day, soundness-sensitive; parked per Q-001. (c) the `mdoc/device` P256 namespace is REQUIRED, not waste: measured 18 of 215 preprocessed columns (the log-13 hinted-mul schedule set) differ between the issuer and device signatures, so dropping it aliases the device onto the issuer schedule. Net: Q-001's option 1 + option 1 confirmed; only two clarifying `mdoc.rs` comments added recording these measurements. Combined accepted waste stays 529,792 cells (< 1.0M threshold).

WO-S4/Q-024 note: production SHA GKR tie-back is reverted on current Stwo because the metric of record is single-thread SHA prove wall time, and the P-3 merged path measured `1.0046 s -> 1.2311 s` despite lower committed cells. Q-025 root cause: marginal SHA interaction columns cost roughly 8-15 ns/cell, while current Stwo LogUp-GKR costs roughly 80 ns/term serial plus a post tie-back tree. Q-026 better-GKR design was copied to `/Users/lucas/stwo/better-gkr.md`; reopening requires upstream/any Stwo build measuring <= 6 ns/term on 2^16 LogUp-GKR, feature-on `BM_ShaZK_equiv/1/prove` beating feature-off by >= 3% with N=5 BENCH-LOCK, and payload under the 2.5 MB ceiling.

GKR-v2 diagnostic (2026-07-04): fused PackedQM31 fraction-add measures 3.8 ns/eff-mult on NEON => ~38 ns/term floor vs <=17 ns break-even. Local stwo GKR acceleration for the SHA tables is closed on mobile-class hardware by arithmetic, not by implementation. Cost of learning this: half a day (the Q-028 kill-switch), vs the +226 ms production regression it would have replayed.

GKR-v2 close-out (2026-07-04): Q-030 chooses stop/no production fusion. The extra Stwo comparison measured the existing `Fraction` abstraction within 3-4% of hand-fused PackedQM31 fraction-add (`log20` median 13.018 ms existing vs 12.563 ms fused), so production fusion is review risk without a consumer. Useful deliverables are the Stwo mixed-height/global-lift correctness fix and `gkr_fraction_add` diagnostic bench; eu-id remains full LogUp with the reopener gates preserved.

| 2026-07-04 | perf/a1r-typed-mults-redo worktree | WO-A1R typed SHA multiplicities | BM_ShaZK_equiv/1/prove (RAYON_NUM_THREADS=1) | 1.0296 s | 1.0194 s (-0.99%) |
| 2026-07-04 | perf/a1r-typed-mults-redo worktree | WO-A1R typed SHA multiplicities | BM_ShaZK_equiv/1/verify (RAYON_NUM_THREADS=1) | 636.92 us | 634.46 us (-0.39%) |
| 2026-07-04 | perf/a1r-typed-mults-redo worktree | WO-A1R typed SHA multiplicities | BM_ShaZK_equiv/33/prove (RAYON_NUM_THREADS=1) | 1.1036 s | 1.1151 s (+1.04%) |
| 2026-07-04 | perf/a1r-typed-mults-redo worktree | WO-A1R typed SHA multiplicities | BM_ShaZK_equiv/33/verify (RAYON_NUM_THREADS=1) | 631.44 us | 633.22 us (+0.28%) |
| 2026-07-04 | feat/a3-hybrid-sha worktree | WO-A3 hybrid SHA | shape_dump SHA cells | 13,843,104 | 5,200,544 (-8,642,560; -62.43%) |
| 2026-07-04 | feat/a3-hybrid-sha worktree | WO-A3 hybrid SHA | shape_dump total identity cells | 37,500,240 | 28,857,680 (-8,642,560; -23.05%) |
| 2026-07-04 | feat/a3-hybrid-sha worktree | WO-A3 hybrid SHA | BM_ShaZK_equiv/1/prove (RAYON_NUM_THREADS=1) | 1.0113 s | 327.12 ms (-67.65%; 3.09x) |
| 2026-07-04 | feat/a3-hybrid-sha worktree | WO-A3 hybrid SHA | BM_ShaZK_equiv/1/verify (RAYON_NUM_THREADS=1) | 619.67 us | 679.37 us (+9.63% vs Phase 0 baseline; Criterion vs previous +7.57%) |
| 2026-07-04 | feat/a3-hybrid-sha worktree | WO-A3 hybrid SHA | BM_ShaZK_equiv/33/prove (RAYON_NUM_THREADS=1) | 1.1028 s | 423.85 ms (-61.56%; 2.60x) |
| 2026-07-04 | feat/a3-hybrid-sha worktree | WO-A3 hybrid SHA | BM_ShaZK_equiv/33/verify (RAYON_NUM_THREADS=1) | 618.97 us | 683.94 us (+10.50% vs Phase 0 baseline; Criterion vs previous +9.73%) |

WO-A1R note: converted the 19 remaining SHA `RelationEntry::new` call sites to typed `RelationEntry::base`; no `unit`, `neg_unit`, or extension-field `new` sites remained in `crates/stwo-sha256`. Parent measurements used `feat/proof-reductions` at `fac1cd4c`; after measurements used the `perf/a1r-typed-mults-redo` worktree before commit. Criterion filters were run separately for block counts 1 and 33 under `RAYON_NUM_THREADS=1`.

WO-A3 note: the proof path removes decode, MajCh, and xor_8 table producers/consumers while retaining split-pack, range, limb-addition, carry, digest, and field-exposure logic. Degree audit required committed duplicate `b/c/f/g` operand bit columns instead of using selector expressions inside Maj/Ch formulas; the duplicate bits are tied to shifted `a/e` bits through linear alias constraints. Schedule lower-sigma output bits are filled for every domain row so ungated sigma formulas remain degree-safe across wraparound and padding rows.

| 2026-07-04 | codex/m4-a3-integration | M4 A3-on-coprocessor convergence | `identity_e2e/prove_identity` (RAYON_NUM_THREADS=1, same-worktree A/B) | 1.8708 s | 922.60 ms (-50.68%) |
| 2026-07-04 | codex/m4-a3-integration | M4 A3-on-coprocessor convergence | `pipeline_e2e` prove (BENCH_ITERS=5, RAYON_NUM_THREADS=1) | 2536 ms | 1194 ms (-52.9%) |
| 2026-07-04 | codex/m4-a3-integration | M4 A3-on-coprocessor convergence | `pipeline_e2e` verify | 41 ms | 41 ms |
| 2026-07-04 | codex/m4-a3-integration | M4 A3-on-coprocessor convergence | `pipeline_e2e` proof bytes | 1,240,046 | 1,186,186 (-53,860) |
| 2026-07-04 | codex/m4-a3-integration | M4 A3-on-coprocessor convergence | mdoc prove (BENCH_ITERS=5, RAYON_NUM_THREADS=1) | 5248 ms | 2089 ms (-60.2%) |
| 2026-07-04 | codex/m4-a3-integration | M4 A3-on-coprocessor convergence | mdoc verify | 45 ms | 45 ms |
| 2026-07-04 | codex/m4-a3-integration | M4 A3-on-coprocessor convergence | mdoc proof bytes | 1,834,614 | 1,809,542 (-25,072) |
| 2026-07-04 | codex/m4-a3-integration | M4 A3-on-coprocessor convergence | mdoc committed shape cells | 56,296,064 | 21,824,128 (-34,471,936; -61.2%) |
| 2026-07-04 | codex/m4-a3-integration | M4 A3-on-coprocessor convergence | identity SHA cells | 13,843,104 | 5,200,544 (-8,642,560; -62.4%) |
| 2026-07-04 | codex/m4-a3-integration | M4 A3-on-coprocessor convergence | identity total cells | 37,500,240 | 28,857,680 (-8,642,560; -23.1%) |
| 2026-07-04 | codex/m4-a3-integration | M4 A3-on-coprocessor convergence | `BM_ShaZK_equiv/1/prove` | 1.0217 s | 324.35 ms (-68.25%) |
| 2026-07-04 | codex/m4-a3-integration | M4 A3-on-coprocessor convergence | `BM_ShaZK_equiv/1/verify` | 646.15 us | 668.77 us (+3.5%) |
| 2026-07-04 | codex/m4-a3-integration | M4 A3-on-coprocessor convergence | `BM_ShaZK_equiv/33/prove` | 1.1069 s | 421.16 ms (-61.95%) |
| 2026-07-04 | codex/m4-a3-integration | M4 A3-on-coprocessor convergence | `BM_ShaZK_equiv/33/verify` | 667.42 us | 676.70 us (+1.4%) |

M4 A3-on-coprocessor note (2026-07-04): Q-M1-005 directed a merge of `feat/a3-hybrid-sha` onto `codex/wo-m3-mdoc-coprocessor` via child branch `codex/m4-a3-integration`, preserving A3 history. Incoming history was limited to A1R typed multiplicities plus A3 SHA changes; conflicts were mechanical perf/status/todo unions only, with no `eu-id-ec-coprocessor`, `stwo-p256`, fork/join, `public_digest_bind.rs`, or toolchain conflict. Same-worktree A/B was run under `/Users/lucas/eu-id/tasks/parity/BENCH-LOCK`; both branches used `nightly-2026-01-15`. Baseline = `codex/wo-m3-mdoc-coprocessor`; candidate = `codex/m4-a3-integration`. Candidate SHA/1 midpoint `324.35 ms` is below A3's `327 ms` reference and clears the >15% regression tripwire. Candidate mdoc prove `2089 ms` lands inside the Q-M1-005 `1.9-2.6 s` sanity band; candidate identity `922.60 ms` lands inside the `0.9-1.2 s` band.

| 2026-07-04 | codex/wo-m5-sha-table-provider-dedup | WO-M5 shared SHA table provider review follow-up | mdoc prove (BENCH-LOCK, BENCH_ITERS=5, RAYON_NUM_THREADS=1) | 2108 ms | 994 ms (-52.8%) |
| 2026-07-04 | codex/wo-m5-sha-table-provider-dedup | WO-M5 shared SHA table provider review follow-up | mdoc verify | 45 ms | 45 ms |
| 2026-07-04 | codex/wo-m5-sha-table-provider-dedup | WO-M5 shared SHA table provider review follow-up | mdoc proof bytes | 1,809,542 | 1,759,326 (-50,216) |
| 2026-07-04 | codex/wo-m5-sha-table-provider-dedup | WO-M5 shared SHA table provider review follow-up | mdoc committed shape cells | 21,824,128 | 6,487,840 (-15,336,288; -70.3%) |
| 2026-07-04 | codex/wo-m5-sha-table-provider-dedup | WO-M5 unchanged identity gate | `pipeline_e2e` prove (BENCH-LOCK, BENCH_ITERS=5, RAYON_NUM_THREADS=1) | 1201 ms | 1200 ms |
| 2026-07-04 | codex/wo-m5-sha-table-provider-dedup | WO-M5 unchanged identity gate | `pipeline_e2e` proof bytes | 1,186,186 | 1,186,186 |
| 2026-07-04 | codex/wo-m5-sha-table-provider-dedup | WO-M5 unchanged SHA gate | `BM_ShaZK_equiv/1/prove` (RAYON_NUM_THREADS=1) | 324.74 ms | 330.64 ms (Criterion: no change) |
| 2026-07-04 | codex/wo-m5-sha-table-provider-dedup | WO-M5 unchanged SHA gate | `BM_ShaZK_equiv/33/prove` (RAYON_NUM_THREADS=1) | 426.17 ms | 430.16 ms |
| 2026-07-06 | f286d3c9 | mdoc Phase D in-circuit MSO bindings | perf-log audit at Phase F start | no Phase D row was present | backfilled audit row; no D-only timing preserved |
| 2026-07-06 | worktree | mdoc Phase V real pyMDOC PID vector gate | `real_vector_pid_pymdoc_end_to_end` prove (RAYON_NUM_THREADS=1, release, ignored) | — | 1412 ms |
| 2026-07-06 | worktree | mdoc Phase V real pyMDOC PID vector gate | `real_vector_pid_pymdoc_end_to_end` verify (RAYON_NUM_THREADS=1, release, ignored) | — | 55 ms |
| 2026-07-06 | worktree | mdoc Phase V real pyMDOC PID vector gate | real pyMDOC PID mdoc proof bytes | — | 2,534,210 |

WO-M5 note (2026-07-04): baseline is `801ea3a5`; candidate is the review-follow-up worktree after baseline commit `34512349`. `mdoc_perf_probe` now emits proof-byte decomposition: total `1,759,326`, STARK `971,649`, coprocessor bundle `787,032`, metadata `645`; inner STARK fields are config `25`, commitments `136`, sampled values `98,400`, decommitments `85,672`, queried values `719,596`, proof-of-work `8`, and FRI proof `67,812`. The review follow-up adds explicit shared-provider claimed-sum tamper, digest/field-exposure tamper, malformed-provider no-panic rejection, and standalone SHA proof-byte pin gates.
