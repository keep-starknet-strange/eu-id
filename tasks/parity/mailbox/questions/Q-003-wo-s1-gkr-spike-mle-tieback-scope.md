---
wo: WO-S1
blocking: true
status: answered
---
## Question
Should WO-S1 be accepted as an honest feature-gated spike/report when the `xor_8` LogUp columns are removed and replaced by a self-contained side GKR proof, or must the WO remain blocked until the GKR verifier artifact is MLE-bound to the committed STARK columns?

## Context
The current `gkr-spike` implementation proves and verifies a 17-instance `xor_8` GKR batch, removes the `xor_8` producer interaction columns and 16 consumer lookup sites, serializes the GKR wire proof in standalone SHA and combined `eu-id-prover::Proof`, and checks output-claim balance plus `partially_verify_batch`.

What is not implemented is the WO step 6/7 tie-back: `GkrArtifact::claims_to_verify_by_instance` is not checked against the committed multiplicity/base-trace columns, and the GKR transcript is not inserted into `air-core` between the interaction commit and a new MLE-eval tree. The WO itself flags the required MLE component as example-only code (`crates/examples/src/xor/gkr_lookups/mle_eval.rs`, 54 KB) and the biggest unknown.

Measured result of this spike:
- `BM_ShaZK_equiv/1/prove` 1.0652s off -> 1.0478s on
- `BM_ShaZK_equiv/1/verify` 612.77us off -> 764.98us on
- committed cells 28,488,480 off -> 28,222,240 on
- SHA interaction cells 5,800,640 off -> 5,534,400 on
- standalone SHA proof bytes 60,045 off -> 73,749 on, including 18,824 GKR bytes

## My best guess
Keep WO-S1 marked blocked, commit the feature-gated spike and measurements, and scope the MLE tie-back as a follow-up architecture task. Treating the current side proof as sound would be wrong because a verifier cannot yet prove that the GKR input-layer claims came from the committed STARK witness.
