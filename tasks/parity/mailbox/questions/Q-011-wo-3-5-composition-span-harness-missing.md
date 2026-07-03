# Q-011 — WO-3.5 composition-span timing harness not found

Date: 2026-07-03
Status: answered
WO: WO-3.5 composition CSE

I implemented conservative hand-CSE in the three requested eval areas:

- `crates/stwo-p256/src/components/hinted_mul/air.rs`
- `crates/stwo-p256/src/components/scalar_mod_mul/component.rs`
- `crates/stwo-sha256/src/constraints.rs`

Verification passed:

- proof bytes before/after are identical:
  - size: 2,321,174 bytes
  - SHA-256: `cfbb39963b664e4d5f4892638db45a414fd46b9640c93ae0f593e73ec09eb2ac`
- `cargo test --workspace --release`: 609 passed, 52 ignored
- BENCH-LOCK Criterion medians:
  - `BM_ECDSAZKProver_equiv/1`: 1.8923s (WO-2.5) -> 1.8129s
  - `BM_ShaZK_equiv/33/prove`: 1.1994s (WO-0) -> 1.1966s

I could not find the composition-span timing harness referenced by the WO. Searches for `CompositionPolynomialGeneration`, `tracing_subscriber`, `tracing::`, `info_span`, and `span!` under `crates/` returned no local harness/subscriber. I did not add a new tracing harness in this WO because that would be new measurement infrastructure beyond the CSE changes.

Question: should a follow-up add a minimal composition-span subscriber/harness for future CSE WOs, or is the Criterion delta plus proof-byte equality sufficient for WO-3.5 close-out?
