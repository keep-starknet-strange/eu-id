# P6 feasibility checkpoint

Date: 2026-08-01

Privacy claim: `public-input unlinkable; transcript zero knowledge pending`

This checkpoint decides whether more witness-generation parallelism can meet
the mobile proving target after P5. It uses measured P4 phone phases and
measured P5 desktop results. The P5 phone sweep is still pending.

## Measured P4 limit

| Device | Prove | Reduction needed for 2,000 ms | Tree 2 write | GKR | Witness |
| --- | ---: | ---: | ---: | ---: | ---: |
| Pixel 8 | 5,664 ms | 64.7% | 1,535 ms | 1,029 ms | 559 ms |
| Galaxy S24 Ultra | 3,884 ms | 48.5% | 1,090 ms | 849 ms | 316 ms |
| Galaxy A54 | 6,062 ms | 67.0% | 1,595 ms | 1,210 ms | 632 ms |

P5 directly targets Tree 2 construction, GKR memory, and runtime controls.
Even if Tree 2 construction and GKR took no time, the remaining totals would
be 3,100 ms, 1,945 ms, and 3,257 ms. This impossible lower bound still misses
the Pixel 8 and Galaxy A54 target.

If witness generation also took no time, the remaining totals would be
2,541 ms, 1,629 ms, and 2,625 ms. Therefore, P5 and P6 cannot meet the Pixel 8
or Galaxy A54 target inside the fixed campaign scope, even under complete
phase deletion.

## P5 evidence

The accepted numerator and claimed-sum work reduced a seven-run desktop median
from 1,236 ms to 1,126 ms. The final denominator-move comparison measured
1,155 ms against an exact 1,146 ms predecessor median. This 0.8 percent change
is not material. The same comparison reduced median peak RSS by 68.25 MiB.

Applying desktop ratios to phones would be a projection, not a phone result.
The expected range after P5 is about 4.2 to 5.2 seconds on Pixel 8, 3.0 to
3.5 seconds on Galaxy S24 Ultra, and 4.7 to 5.5 seconds on Galaxy A54. The
Firebase sweep must replace these projections with measurements.

## P6 decision

Do not add more witness-generation parallelism at this checkpoint.

- Witness generation is 8.1 to 10.4 percent of the measured phone total.
- The canonical witness path already runs the issuer, device, and revocation
  ML-DSA work in parallel.
- Keccak witness construction and SHA trace work already use parallel paths.
- Removing the complete witness phase cannot close the fixed-scope gap on two
  binding devices.

P6 becomes applicable only if the final P5 phone measurements make witness
generation a binding phase and prove that its removal could cross the target.
Otherwise, P6 remains intentionally empty.

## Audited alternatives

The existing branches contain no compatible two-fold or three-fold proving
improvement. The remaining material alternatives require at least one forbidden
scope change: a new STWO backend or pin, lower circuit geometry, weaker PCS
parameters, a different ML-DSA profile, or a weaker device target. Reusing a
presentation commitment is not acceptable because it would harm unlinkability.

The campaign will still complete P5 and report the best measured phone result.
It will not weaken the theorem, transcript binding, ML-DSA-65 role set, or
unlinkability to claim the 2,000 ms target.
