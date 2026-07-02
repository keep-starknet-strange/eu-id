---
wo: WO-1.8
blocking: false
status: open
---
## Question
Should WO-1.8 keep `lto = "fat"` and `codegen-units = 1` in `[profile.bench]` only, rather than `[profile.release]`, because release LTO breaks the P-256 monolithic proof gate?

## Context
Literal WO-1.8 step 2 put the flags in `[profile.release]` with `[profile.bench] inherits = "release"`.
After that change, the required gate failed:

`cargo test --workspace --release`

Focused repro:

`cargo test -p stwo-p256 --release proof::tests::current_p256_proof_pipeline_proves_and_verifies_current_air_monolithic_proof -- --exact --nocapture --test-threads=1`

failed with:

`current AIR monolithic proof proves: ProofLayer("Constraints not satisfied.")`

The same focused test passed when run with:

`CARGO_PROFILE_RELEASE_LTO=false CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16`

The benchmark improvements were measured under Cargo's bench profile, so moving the flags to `[profile.bench]` preserves the bench win while keeping release tests on the known-good profile.

## My best guess
Keep LTO/CU1 in `[profile.bench]` only. The handover hard rule says `cargo test --workspace --release` must be green before marking a WO done, and a bench-only profile still implements the build-level benchmark optimization without changing proof semantics under the release test profile.
