# Q-012 — WO-1.6 twiddle cache is proof-identical but second prove did not speed up

Date: 2026-07-03
Status: answered
WO: WO-1.6 prove caches

Implemented the safest cache from the WO:

- `air_core::prove` now caches `SimdBackend::precompute_twiddles(...)` by `twiddle_log_size` via `std::sync::OnceLock`.
- Cache values are leaked process-lifetime `TwiddleTree<SimdBackend>` references and are read-only after first initialization.

Verification:

- `wo_1_6_repeated_prove_bytes_identical`: passed.
- `cargo test --workspace --release`: 609 passed, 54 ignored.
- Cold path `BM_ECDSAZKProver_equiv/1`: 1.8129s (WO-3.5) -> 1.8059s, no significant change.

Warm-cache timing diagnostics did **not** show a second-call win:

- run 1: first 818.426ms, second 856.221ms, delta -37.796ms
- run 2: first 814.184ms, second 826.154ms, delta -11.969ms

Per WO guidance, I stopped rather than adding speculative preprocessed/tree caches. The likely interpretation is that twiddle precompute is below noise for this pipeline, and the remaining scoped wins require broader preprocessed-column cache plumbing or upstream tree-0 injection support.

Question: should WO-1.6 be considered closed as "safe cache, no measurable win", or should a follow-up implement the larger preprocessed-column caches despite the first accepted cache being flat/negative?
