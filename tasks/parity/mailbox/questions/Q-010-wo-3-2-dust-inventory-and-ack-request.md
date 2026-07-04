# Q-010 — WO-3.2 dust inventory drift + merge-group ack request

Date: 2026-07-03
Status: answered
WO: WO-3.2 component-dust merge

## Context

After WO-2.5 (`49979dc7` implementation, `583006db` ledger), I ran:

```bash
cargo test -p eu-id-prover --release shape_dump -- --ignored --nocapture
```

P-256 shape is now:

- component count: 45
- p256 cells: 13,262,896
- total cells: 27,177,760

The WO says to inventory P-256 components with `total <= 10` cols and log size 4..9, then wait for architect ack before implementing any merge.

## Strict log-4..9 dust inventory

These are the only P-256 components matching `total <= 10` and `max_col_log` in `4..=9`:

| idx | component | eval | relation/equation | cols | max log |
|---:|---|---|---|---:|---:|
| 2 | `scalar_setup.range9` | `RangeCheckEval` | `scalar_setup.range9` / 9-bit range table | 6 | 9 |
| 3 | `scalar_setup.signed_carry` | `SignedCarryRangeEval` | `scalar_setup.signed_carry` / `SCALAR_SETUP_SIGNED_CARRY_EQUATION` | 7 | 4 |
| 13 | `scalar_mod_muls.signed_carry` | `SignedCarryRangeEval` | `scalar_mod_mul.signed_carry` / scalar-mod-mul signed carry equation | 7 | 7 |
| 30 | `prepared_point_range7` | `RangeCheckEval` | `range7` / 7-bit range table | 6 | 7 |
| 39 | `hinted_mul.signed_h` | `SignedCarryRangeEval` | `hinted_signed_h` / `HINTED_MUL_H_HI_EQUATION` | 7 | 5 |

I do **not** see a strict mergeable group here:

- idx 13 and idx 30 both have log 7, but one is signed-carry and one is plain range-check, so the preprocessed columns and eval shape differ.
- all other strict dust rows have unique log sizes and/or equations.

## Broader `total <= 10` inventory

If the intended WO scope is all small provider components regardless of log size, the current broader inventory is:

| idx | component | eval | cols | max log |
|---:|---|---|---:|---:|
| 1 | `scalar_setup.range13` | `RangeCheckEval` | 6 | 13 |
| 2 | `scalar_setup.range9` | `RangeCheckEval` | 6 | 9 |
| 3 | `scalar_setup.signed_carry` | `SignedCarryRangeEval` | 7 | 4 |
| 12 | `scalar_mod_muls.range13` | `RangeCheckEval` | 6 | 13 |
| 13 | `scalar_mod_muls.signed_carry` | `SignedCarryRangeEval` | 7 | 7 |
| 30 | `prepared_point_range7` | `RangeCheckEval` | 6 | 7 |
| 35 | `public_key_on_curve.range13` | `RangeCheckEval` | 6 | 13 |
| 36 | `projective_signed_carry` | `SignedCarryRangeEval` | 7 | 18 |
| 38 | `hinted_mul.range13` | `RangeCheckEval` | 6 | 13 |
| 39 | `hinted_mul.signed_h` | `SignedCarryRangeEval` | 7 | 5 |
| 40 | `hinted_mul.signed_formula` | `SignedCarryRangeEval` | 7 | 18 |
| 44 | `final_add.range13` | `RangeCheckEval` | 6 | 13 |

Candidate groups outside strict log-4..9:

1. **log-13 plain range providers**: idx 1, 12, 35, 38, 44 (`RangeCheckEval`, same range table domain, distinct `RangeCheckRelation`s). Merge estimate: 5 components -> 1, 4 fewer component eval/mask/commit overhead units, 0 cell change.
2. **log-18 signed-carry providers**: idx 36, 40 (`SignedCarryRangeEval`, same projective signed-carry equation/domain after WO-2.5 preprocessed dedup, distinct relations). Merge estimate: 2 components -> 1, 1 fewer overhead unit, 0 cell change.

## Question

WO-3.2 asks for architect ack before implementing one group.

Which path should I take?

1. Treat the strict log-4..9 inventory as the binding scope: **no mergeable group exists**, mark WO-3.2 blocked/done-as-report.
2. Approve the broader log-13 range-provider group (idx 1/12/35/38/44) for implementation despite being outside the title's log-4..9 band.
3. Approve the broader log-18 signed-carry group (idx 36/40) for implementation.

Until answered, I am not implementing a WO-3.2 merge.
