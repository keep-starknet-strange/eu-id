# WO-S2 — EC mul committed-cell floor

Date: 2026-07-03

Source note: I could not fetch the IACR ePrint PDF from this environment; the direct `eprint.iacr.org/2024/2010.pdf` request returned Cloudflare HTML. I therefore use the WO's quoted Longfellow premise as the paper-side input: ~1,085 committed witness values for one ECDSA verification, with hinted double-and-add point outputs plus 7 precomputed table points, checked by quadratic relations.

## Current shape

Fresh command:

```bash
rtk proxy cargo test -p eu-id-prover --release shape_dump -- --ignored --nocapture
```

P-256 per signature from `shape_dump`:

| family | cols | cells | notes |
|---|---:|---:|---|
| preprocessed | 215 | 775,088 | log 4..18 tables/schedules |
| trace | 3,788 | 4,270,976 | witness + multiplicities |
| interaction | 2,440 | 9,527,552 | SecureField LogUp columns |
| total | 6,443 | 14,573,616 | P-256 only |

Cost model: current single-thread P-256 prove time is about 565 ms. Counting interaction cells as 2x base/preprocessed cells gives:

`weighted_current = 775,088 + 4,270,976 + 2 * 9,527,552 = 24,101,168`

So the measured rate is `565 ms / 24.10M = 23.4 ns` per weighted cell. The <=17 ms target corresponds to about `725k` weighted cells.

Local arithmetic constants: P-256 values use `N_LIMBS = 20`, `LIMB_BITS = 13`. Current hinted field multiplication uses 373 base columns per active mul row plus LogUp interactions; with GKR lookups available, the base floor is still 373 committed cells per field-mul row. RCB point add/double uses up to 15 field mul rows, so one checked EC transition costs about `15 * 373 = 5,595` arithmetic cells before point/state columns.

## Candidate A: current fake-GLV ladder + GKR lookups

Assumption: every current P-256 LogUp interaction column is replaced by sound GKR lookup machinery with no committed interaction columns. Multiplicity, schedule, witness, and preprocessed cells remain.

| family | cells |
|---|---:|
| preprocessed | 775,088 |
| trace | 4,270,976 |
| interaction | 0 |
| total | 5,046,064 |

Degree families:

| constraint family | degree |
|---|---:|
| current boolean/schedule gates | <=2 |
| hinted-mul random-z identities | <=2 |
| formula muxed reductions/equalities | <=3 |
| GKR lookup tie-backs | <=3 MLE/prefix constraints |

Projected prove time: `5.046M * 23.4 ns = 118 ms`. This is a useful reduction from 565 ms, but still ~7x above 17 ms.

## Candidate B: windowed mul with hinted jump tables

Soundness condition: a lookup into a prover-supplied table is not enough. Either the table is fixed/public, or every hinted table point must be constrained as the claimed multiple of the relevant base. For verifier public key `Q`, the table is per signature and must be proven.

Model:
- two scalar multiplications per ECDSA verification: `u1 * G` and `u2 * Q`;
- jump table layout: one table per window containing `(2^w - 1)` affine points for that base and window shift;
- table point cells: `2 bases * ceil(256/w) windows * (2^w - 1) points * 40 limbs`;
- selected accumulator step cells: `2 * ceil(256/w) * (15 * 373 + 104)`, where 104 covers accumulator/table/output point limbs and flags outside the hinted mul rows;
- sound table construction cells: one checked EC recurrence per nonzero table point, costed at the same `15 * 373 + 104`.

| w | selected-step cells | table point cells | table-validity cells | total cells |
|---:|---:|---:|---:|---:|
| 4 | 729,472 | 76,800 | 10,942,080 | 11,748,352 |
| 8 | 364,736 | 652,800 | 93,007,680 | 94,025,216 |
| 16 | 182,368 | 83,884,800 | 5,976,076,800 | 6,060,143,968 |

The w=16 row is intentionally shown as a blow-up case: dense per-window tables are impossible once table validity is enforced. If table validity were incorrectly trusted, w=4 would land near 0.81M cells, but that violates the WO's soundness rule.

Degree families:

| constraint family | degree |
|---|---:|
| scalar window digit range/selection via GKR | <=3 tie-back |
| table lookup membership via GKR | <=3 tie-back |
| table recurrence EC add/double | hinted mul <=2, mux/reduction <=3 |
| accumulator update | hinted mul <=2, mux/reduction <=3 |

Best sound projection here is w=4: `11.75M * 23.4 ns = 275 ms`. The binding cost is proving the per-signature public-key table, not selecting from it.

## Candidate C: Longfellow-mimic point-output trace

Model:
- commit per-iteration point outputs rather than dense per-window tables;
- use the WO's Longfellow witness-count premise as the point/state floor: `1,085 field values * 20 limbs = 21,700 M31 cells`;
- range checks are GKR-backed, so no committed range interaction columns;
- every EC transition still needs non-native P-256 arithmetic over M31. Using the current sound RCB/hinted-mul primitive gives `256 iterations * 15 mul rows * 373 cells = 1,432,320`;
- add the witness-value floor: total about `1,454,020` cells.

Degree families:

| constraint family | degree |
|---|---:|
| point limb range/canonicality via GKR | <=3 tie-back |
| on-curve/final-result checks | field mul identities <=2 plus linear reductions |
| per-iteration add/double formula | hinted mul <=2, muxed formula constraints <=3 |
| scalar bit/window use | boolean/range <=2 or GKR lookup <=3 tie-back |

Projected prove time: `1.454M * 23.4 ns = 34 ms`.

This is the best sound floor among the three using today's M31 non-native arithmetic. To reach 17 ms, the EC transition cost must fall below about `725k` weighted cells total, i.e. less than half of the current 15-hinted-mul-per-iteration model. That requires a new arithmetic representation, not just removing LogUp columns.

## Verdict

ECDSA-1 single-thread <= 17 ms on M-class is infeasible with the sound layouts counted here. The closest layout is the Longfellow-mimic point-output trace at ~1.45M committed cells and ~34 ms projected prove time. The binding constraint is non-native P-256 multiplication over 20 13-bit M31 limbs under the D<=3/log+1 rule, not lookup interaction columns.
