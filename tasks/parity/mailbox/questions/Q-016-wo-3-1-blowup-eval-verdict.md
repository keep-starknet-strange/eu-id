# Q-016 — WO-3.1 blowup 2→1 verdict

Date: 2026-07-03
Status: answered
WO: WO-3.1 blowup 2→1 evaluation
Blocking: no

Live source profile is post-WO-0 128-bit:

```text
pow_bits = 10
FriConfig::new(5, 2, 59, 1)
```

I evaluated the fair 128-bit blowup-1 comparison using the feature-gated `fri_sweep` harness from `1755fd22`, with `RAYON_NUM_THREADS=1 FRI_SWEEP_SAMPLES=1` under `BENCH-LOCK`.

Matched comparison (`pow=10`, `log_last_layer=5`, `fold_step=1`):

| config | queries | prove ms | verify ms | proof bytes | composition ms |
|---|---:|---:|---:|---:|---:|
| blowup 2 | 59 | 3031.992 | 20.866 | 2,302,954 | 909.354 |
| blowup 1 | 118 | 2350.327 | 28.929 | 4,243,266 | 904.634 |

Deltas:

- Prove improves by 681.665 ms (22.48%).
- Proof bytes grow by 1,940,312 bytes (84.25%).
- Verify regresses by 8.063 ms (38.63%).

Verdict: reject/no-change for now. Blowup 1 is a real prover-time win, but the proof-size increase is large and WO-3.1 requires an architect-named mobile proof-size ceiling plus explicit production-config ack before accepting. Neither exists in the current mailbox state, so I left production `PcsConfig` unchanged.
