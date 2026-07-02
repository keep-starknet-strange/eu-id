# Parity work — status ledger

One line per completed/blocked WO. Format: `WO-id | date | commit | result (metric before → after)`

WO-1.8 | 2026-07-02 | 603519d0 | bench-only LTO/CU1 + RUSTFLAGS native + bench mimalloc; BM_ECDSAZKProver/1 2.258s → 1.894s, SHA/1 1.393s → 1.055s, SHA/33 1.525s → 1.154s, pipeline/prove 933ms → 700ms; cargo test --workspace --release passed (604 passed, 49 ignored)
