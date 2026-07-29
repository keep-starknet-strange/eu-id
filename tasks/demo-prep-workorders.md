# Demo-prep work orders — unlinkability acceptance addendum

This worktree was created from `feat/quantum-safe` commit `abf9c27f`, where
the untracked campaign copy of the broader demo-prep work orders was not
present. This addendum records the baseline update required by mailbox answer
`A-727-unlinkability-u0-stop-go.md` without modifying another worktree.

## Post-Stwo-repin demo baseline — 2026-07-29

Branch `codex/unlinkability`, isolated repin commit
`821d8c7d967043678d0c7486a40377937d0b06bc`, Stwo family pinned to
`4f39939eacd0c5efc8ee157e4215a250ca29168f`.

Cold fresh-process measurements, one iteration per process and no
`RAYON_NUM_THREADS` override:

| path | prove ms ×3 | fresh verify ms ×3 | wire/envelope bytes ×3 |
|---|---|---|---|
| product `identity_probe` | 507 / 511 / 513 | 74 / 74 / 80 | 956,456 / 948,610 / 948,514 |
| TS13 `pq_perf_probe` | 500 / 490 / 487 | 37 / 34 / 38 | 977,120 / 983,218 / 984,386 |

The product path therefore improves from the previously quoted 587–616 ms
prove / 76–79 ms verify / ~952 KB envelope baseline to 507–513 ms prove /
74–80 ms verify / 948,514–956,456 B. All three runs reported
`dob_cbor_in_envelope=false` and `dob_ascii_in_envelope=false`.

The TS13 path improves from 678–702 ms prove / 80–85 ms verify / ~971 KB
compressed wire to 487–500 ms prove / 34–38 ms fresh verify /
977,120–984,386 B compressed wire. Raw proof bytes were intentionally not
compared with the compressed wire baseline.

## Phase-1 compatibility coordination

Mailbox A-730 authorizes a single product V7 / TS13 V3 compatibility cut only
after the unlinkability layout is frozen. The table above remains explicitly
the pre-cut V6/V2 baseline and must not be presented as measurements of the
new envelope.

The frozen V7/V3 cut was measured in three cold fresh release processes, one
iteration per process and no `RAYON_NUM_THREADS` override:

| path | prove ms ×3 | fresh verify ms ×3 | wire/envelope bytes ×3 |
|---|---|---|---|
| product V7 `identity_probe` | 609 / 615 / 627 | 85 / 86 / 86 | 1,248,787 / 1,247,593 / 1,238,851 |
| TS13 V3 `ts13_sdk_perf_probe` | 851 / 887 / 847 | 93 / 94 / 95 | 1,229,490 / 1,228,810 / 1,229,517 |
| TS13 core `pq_perf_probe` | 742 / 769 / 759 | 48 / 49 / 42 | 1,213,977 / 1,220,424 / 1,217,117 |

The TS13 core byte column is the Bzip2 proof wire size; its corresponding raw
proof sizes are 1,552,867 / 1,557,427 / 1,555,443 bytes. These are the
post-cut demo-prep numbers. The compatibility measurement prerequisite is now
satisfied; merging onto a demo-quoted branch still requires the normal
explicit integration approval.
