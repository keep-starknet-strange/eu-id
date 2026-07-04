---
wo: WO-2.1
blocking: true
status: answered
---
## Question
For WO-2.1, should the SHA split-table merge steps be abandoned/re-scoped because the current table contents are not identical, or should we implement a different merged component shape with relation-specific output columns?

## Context
WO-2.1 says M1 and M2 are mechanical merges, "one preprocessed group" with the existing multiplicity/interaction columns, and says to verify content identity first.

The identity checks fail on the current code:

- M1 σ split tables:
  - `lsigma0_lo` vs `lsigma0_hi`: first mismatch at `key=1`: `(key, s, sp) = (1, 0, 1)` vs `(1, 1, 0)`
  - `lsigma0_lo` vs `lsigma1_lo`: first mismatch at `key=2`: `(2, 0, 2)` vs `(2, 1, 0)`
  - `lsigma0_lo` vs `lsigma1_hi`: first mismatch at `key=2`: `(2, 0, 2)` vs `(2, 1, 0)`
- M2 round split tables:
  - `sigma0_lo` vs `sigma0_hi`: first mismatch at `key=1`: `(1, 1, 0, 0, 0)` vs `(1, 0, 0, 1, 0)`
  - `sigma0_lo` vs `sigma1_lo`: first mismatch at `key=1`: `(1, 1, 0, 0, 0)` vs `(1, 0, 1, 0, 0)`
  - `sigma0_lo` vs `sigma1_hi`: first mismatch at `key=4`: `(4, 0, 0, 1, 0)` vs `(4, 0, 0, 0, 1)`

The later WO text also appears stale against the current implementation:

- `Xor8` is not an 8-bit table padded to log16; `build_xor_8_table` enumerates all `(x, y)` byte pairs, so it genuinely has `256 * 256 = 2^16` rows.
- `MajCh` currently uses `group_width = 6` packed group values, not 16-bit limbs, so the described 16-bit-to-two-byte split does not match the current table shape.

## My best guess
Do not implement the mechanical M1/M2/M3 merges in this tree. A sound replacement would need a new scoped WO that explicitly changes the relation/component shape, for example a wider shared table with relation-specific output columns or a different split strategy. I would leave `Xor8` at log16 and leave `MajCh` unchanged unless a new WO specifies the current `group_width = 6` design.
