# Q-015 — WO-3.3 FRI sweep recommendation

Date: 2026-07-03
Status: open
WO: WO-3.3 FRI config sweep
Blocking: no

WO-3.3 is implemented in `693e8596` with a feature-gated `fri_sweep` example and no production profile change.

Acceptance run:

```text
RAYON_NUM_THREADS=1 FRI_SWEEP_SAMPLES=1 cargo run -p eu-id-prover --release --example fri_sweep --features fri-sweep
```

The `fold_step=2` probe verified, so the sweep included `fold_step = {1, 2}`. All 36 candidates proved and verified through the sweep-only explicit-config path.

Pareto rows:

| pow | blowup | queries | last | fold | median ms | proof bytes | composition ms | current |
|---:|---:|---:|---:|---:|---:|---:|---:|:---:|
| 20 | 3 | 36 | 5 | 2 | 4436.177 | 1482322 | 906.681 |  |
| 20 | 3 | 36 | 1 | 2 | 4260.264 | 1485666 | 992.969 |  |
| 10 | 3 | 40 | 1 | 2 | 4119.903 | 1620562 | 902.669 |  |
| 20 | 2 | 54 | 5 | 2 | 2879.226 | 2068594 | 913.078 |  |
| 10 | 2 | 59 | 1 | 2 | 2857.298 | 2237338 | 903.628 |  |
| 20 | 1 | 108 | 1 | 2 | 2244.784 | 3804002 | 917.187 |  |
| 10 | 1 | 118 | 5 | 2 | 2223.488 | 4126530 | 904.816 |  |

Current production row (`pow=10, blowup=2, queries=59, last=5, fold=1`): 3122.511 ms, 2,302,954 bytes, 917.782 ms `CompositionPolynomialGeneration`.

Recommendation if the objective is smallest proof bytes: `pow=20, log_blowup=3, n_queries=36, log_last_layer=5, fold_step=2`.

Tradeoff: proof bytes drop 2,302,954 -> 1,482,322 (-820,632 bytes, -35.63%), but one-sample prove time regresses 3122.511 ms -> 4436.177 ms (+1.313666 s). I did not commit this profile change because HANDOVER keeps production config changes sanctioned-only.
