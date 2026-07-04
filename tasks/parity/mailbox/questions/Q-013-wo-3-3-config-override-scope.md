# Q-013 — WO-3.3 needs ack on sweep-only PcsConfig override plumbing

Date: 2026-07-03
Status: answered
WO: WO-3.3 FRI config sweep

The WO requires a sweep harness that proves the combined identity fixture under candidate `PcsConfig`s without changing the production profile. I inspected the current path:

- `eu_id_prover::prove_with_column_breakdown(...)` constructs `P256Prover`, then uses `let config = p256.pcs_config();`.
- The combined proof then calls `air_core::prove(&mut modules, config)`.
- `P256Prover::pcs_config()` derives from the hardcoded P-256 production profile.

So the sweep needs an explicit override path around the combined proof construction. Options I see:

1. Add a public or crate-private `prove_with_column_breakdown_and_config(..., config: PcsConfig)` used only by `examples/fri_sweep.rs`.
2. Add a config override field/method on `P256Prover` so `pcs_config()` can return the override.
3. Add an example-local copy of the combined prove assembly, which avoids production API changes but duplicates load-bearing module ordering.

The WO says: "If threading it is non-trivial, mailbox it before coding." This is non-trivial because module order/transcript config is load-bearing and the config gate is sanctioned-change-only.

Question: which override shape do you want for the FRI sweep harness?

My recommendation is option 1: a crate-private helper in `eu-id-prover` that keeps the production `prove(...)` unchanged and makes the sweep override explicit at the call site.
