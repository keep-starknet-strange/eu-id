# Q-015 — WO-3.3 FRI sweep recommendation

Date: 2026-07-03
Status: answered
WO: WO-3.3 FRI config sweep
Blocking: no

WO-3.3 is implemented in `693e8596` / corrected by `1755fd22` with a feature-gated `fri_sweep` example and no production profile change.

Acceptance run:

```text
RAYON_NUM_THREADS=1 FRI_SWEEP_SAMPLES=1 cargo run -p eu-id-prover --release --example fri_sweep --features fri-sweep
```

The `fold_step=2` probe verified, so the sweep included `fold_step = {1, 2}`. All 36 candidates proved and verified through the sweep-only explicit-config path. The corrected harness reports prove and verify timing separately.

Pareto rows:

| pow | blowup | queries | last | fold | prove ms | verify ms | proof bytes | composition ms | current |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|:---:|
| 20 | 3 | 36 | 5 | 2 | 4194.932 | 17.844 | 1482322 | 879.103 |  |
| 20 | 3 | 36 | 1 | 2 | 4103.681 | 17.427 | 1485666 | 888.696 |  |
| 10 | 3 | 40 | 1 | 2 | 4075.007 | 17.913 | 1620562 | 888.154 |  |
| 0 | 3 | 43 | 5 | 2 | 4066.911 | 18.551 | 1720794 | 876.205 |  |
| 20 | 2 | 54 | 5 | 2 | 2933.393 | 19.915 | 2068594 | 920.203 |  |
| 10 | 2 | 59 | 5 | 2 | 2841.778 | 20.341 | 2230794 | 907.422 |  |
| 0 | 2 | 64 | 1 | 2 | 2814.542 | 20.944 | 2404498 | 899.766 |  |
| 20 | 1 | 108 | 1 | 2 | 2170.960 | 26.940 | 3804002 | 883.580 |  |
| 10 | 1 | 118 | 5 | 2 | 2168.225 | 27.433 | 4126530 | 895.015 |  |
| 0 | 1 | 128 | 5 | 2 | 2162.480 | 28.395 | 4443458 | 900.890 |  |

Current production row (`pow=10, blowup=2, queries=59, last=5, fold=1`): 3031.992 ms prove, 20.866 ms verify, 2,302,954 bytes, 909.354 ms `CompositionPolynomialGeneration`.

Recommendation if the objective is smallest proof bytes: `pow=20, log_blowup=3, n_queries=36, log_last_layer=5, fold_step=2`.

Tradeoff: proof bytes drop 2,302,954 -> 1,482,322 (-820,632 bytes, -35.63%), but one-sample prove time regresses 3031.992 ms -> 4194.932 ms (+1.162940 s). Verify time improves 20.866 ms -> 17.844 ms. I did not commit this profile change because HANDOVER keeps production config changes sanctioned-only.
