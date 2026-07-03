# Parity work — status ledger

One line per completed/blocked WO. Format: `WO-id | date | commit | result (metric before → after)`

WO-1.8 | 2026-07-02 | e72cc328 | bench-only LTO/CU1 + RUSTFLAGS native + bench mimalloc; BM_ECDSAZKProver/1 2.258s → 1.894s, SHA/1 1.393s → 1.055s, SHA/33 1.525s → 1.154s, pipeline/prove 933ms → 700ms; cargo test --workspace --release passed (604 passed, 49 ignored)
WO-1.7 | 2026-07-02 | 80dabe23 | rayon 1.12.0 / rayon-core 1.13.0 already latest; SHA prover now stores polynomial coefficients to bypass the deadlocking Stwo barycentric-weight path; 3 contended 30-min soaks passed (41/48/46 sha/prove iterations), identity_bench --features parallel -- 'prove' passed, longfellow_equiv_bench passed, cargo test --workspace --release passed (604 passed, 49 ignored)
WO-1.1 | 2026-07-02 | 4ee92b6b | blocked on Q-002: scoped hint/draft generation improved (`hint_gen_timing` 323.335ms → 157.269ms with RAYON_NUM_THREADS=1; 192.371ms → 58.347ms default Rayon), serial-vs-parallel draft equality passed, cargo test -p stwo-p256 --release passed (319 passed, 11 ignored), cargo test -p eu-id-prover --release passed (18 passed, 18 ignored), cargo test --workspace --release passed (605 passed, 50 ignored); required BM_ECDSAZKProver_equiv/1 stayed 1.894s → 1.874s because the harness prebuilds drafts outside the timed loop
