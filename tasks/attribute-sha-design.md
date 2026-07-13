# Attribute-only SHA compaction design

## Scope and production load

After Q2, the product has two SHA-256 consumers, both for issuer-signed attribute payloads:

| Attribute | Encoded item | Padded blocks | Active SHA rows | Exposure yields | Byte columns | Target blocks |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| birth date | 92 bytes | 2 | 128 | 39 | 40 | 0, 1 |
| nationality | 85 bytes | 2 | 128 | 32 | 36 | 0, 1 |

The two consumers occupy separate 256-row slots in one log-9 merged trace. Before Q3 the merged
SHA committed 12 preprocessed, 642 trace, and 444 interaction columns (1,098 total; 562,176 cells).
Its shared tables committed another 88 columns / 9,306,656 cells. Of those shared-table cells,
8,388,608 belonged to eight split-pack producers.

## Minimum replacement

Keep the existing hybrid bit AIR and delete the split-pack lookup family that it superseded:

1. Store one field selector per distinct target block, rather than one identical selector per
   yielded byte. Every yield targeting a block reuses that block's selector.
2. Delete the 16 round Maj/Ch packed-output columns, eight schedule sigma-input packed columns,
   and 32 block-input auxiliary packed columns.
3. Delete their 24 consumer lookup sites per SHA row and all eight 2^16-row split-pack producers.
4. Keep the SHA algorithm, message padding, digest/field relations, transcript ordering of all
   surviving components, and the range tables unchanged.

This is a deletion of redundant representations, not a new SHA construction.

## Soundness rails

The removed values do not uniquely constrain any SHA word:

- `W`, `a`, `b`, `c`, `e`, `f`, and `g` retain 32 boolean columns each. Separate low/high
  recomposition equations bind each 16-bit limb to its corresponding 16 bits.
- Schedule `sigma0` and `sigma1` retain 32 boolean output columns each. Their bits equal the direct
  rotate/xor expressions over the shifted `W` bits, and separate low/high recompositions bind the
  result limbs on active schedule rows.
- `Maj` and `Ch` limbs retain direct recomposition from the multilinear boolean expressions over
  `a,b,c` and `e,f,g`.
- The shifted aliases `b=a@-1`, `c=a@-2`, `f=e@-1`, and `g=e@-2`, including the round-0/1 block
  boundary cases, remain constrained on bit columns.
- Carry `Range2/4/5` lookups and terminal digest-limb `Range16` lookups remain unchanged.

Low and high limbs must remain separate equations. Replacing them with one 32-bit equation would
allow a compensating limb shift and is outside this design.

The shared selector remains tied to the existing block counter and slot selector. Selector sharing
only merges witnesses that previously had identical block-target constraints; it does not change
the number or multiplicity of field relation yields. As before, provider completeness is closed by
the composed LogUp consumer.

## Degree and transcript worksheet

- Booleanity remains degree 2.
- Direct `Ch`/`Maj` bit expressions remain degree at most 3.
- Gating a linear limb recomposition remains within the existing degree budget.
- Deleting packed-expression equalities and LogUp terms cannot raise the maximum constraint degree.
- The main consumer lookup count falls from 66 to 42 base sites per row. With batch size four, the
  base interaction width falls by 24 columns.
- The eight split-pack relation challenges, producer claims, multiplicity columns, fixed value
  columns, interaction columns, and component descriptors are removed together. The surviving
  relation draw and component orders are pinned by prover/verifier round-trip tests.

## Column and cell model

Split-pack deletion saves 56 merged trace columns, 24 merged interaction columns, and 64 shared
table columns. Per-block selector sharing saves another 67 merged trace columns for the production
loads (birth-date tail 80 to 43; nationality tail 69 to 39).

Expected merged consumer width: `1,098 - 56 - 24 - 67 = 951` columns at log 9.

Expected SHA footprint, excluding the selector saving, is 1,439,264 cells instead of 9,868,832:
an 8,429,568-cell (85.4%) reduction. Selector sharing removes another 34,304 log-9 cells from the
merged consumer.

The post-change shape dump matches the model exactly: 12 preprocessed + 519 trace + 420 interaction
= 951 merged SHA columns at log 9. The first A/B omitted the required `RAYON_NUM_THREADS=1` and was
therefore a default-Rayon multithreaded comparison, not the campaign's one-thread metric.

The corrected same-session five-run A/B pins `RAYON_NUM_THREADS=1` against parent `4c25c72d`.
Baseline medians are 8,573 ms prove, 16 ms verify, and 1,113,514 bytes; Q3 medians are 6,995 ms,
15 ms, and 1,081,410 bytes. Median proving improves 18.4% and proof size improves 32,104 bytes
(2.88%).

## Verification matrix

- Differential digests against `sha2` at production lengths and padding boundaries.
- Selector allocation/sharing tests, including multiple yields in the same block and two target
  blocks in one field.
- Constraint-negative tests for message, schedule, round state, padding, digest, field byte,
  selector, and slot tampering.
- Standalone and shared-table proof round trips, including multi-slot composition.
- Workspace check, strict clippy, formatting, product test suites, AIR shape dump, and repeated
  single-thread release probes.
