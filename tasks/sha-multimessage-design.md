# S8 — Multi-message (slot-scheduled) SHA-256 consumer instance

Goal: merge the three log-8 SHA-256 consumer instances of the quantum-safe
mdoc composition (revocation + 2 attributes) into ONE multi-slot instance at
log 10, recovering the duplicated base-trace and base-interaction columns.
Wire format change acceptable; P-256 mode untouched.

## 0. Mode decision (required by the task statement)

**The multi-slot path is a separate prover/verifier pair
(`Sha256MultiProver` / `Sha256MultiVerifier`) used ONLY by the quantum
composition.** The single-message `Sha256Prover`/`Sha256Verifier` and the
`Sha256Eval` single-slot code paths are byte-for-byte untouched, so every
P-256 suite and its proofs are unchanged. `Sha256Eval` grows an
`Option<MultiSlotConfig>`; `None` (the only value the legacy constructors can
produce) takes exactly the existing code paths.

## 1. Property specification

Let the schedule be `n_slots` uniform regions of `2^slot_log` rows each
(`slot_rows`), region `s` = rows `[s·slot_rows, (s+1)·slot_rows)`, laid over a
`2^log_n_rows`-row trace, `n_slots · slot_rows ≤ 2^log_n_rows`. Slot
boundaries are 64-row (block) aligned by construction (`slot_log ≥ 6`).

The merged trace is honest iff, for every slot `s` with message `m_s`
(`n_s = blocks(pad(m_s))`, `64·n_s < slot_rows` — every slot keeps at least
one in-slot 64-row padding region):

1. Rows `[s·slot_rows, s·slot_rows + 64·n_s)` are an honest single-message
   SHA-256 trace of `m_s` exactly as specified for the existing single
   instance: IV at the slot's first block, §10.3 chain within the slot,
   round/schedule/finalization identities per row, §10.4 padding-role
   identities per block.
2. `is_last_block` is 1 exactly on the t=63 row of block `n_s−1` of each
   slot (and nowhere else); slot `s`'s digest bytes are yielded on its
   `SlotIoRelations[s].digest` channel iff `slots[s].expose_digest`.
3. Slot `s`'s field-exposure yields `(field_id, byte_index, byte)` fire only
   from rows of region `s`, against `SlotIoRelations[s].field`, with every
   exposed byte range-pinned to [0,256) — identical contract to the single
   instance (the revocation message bytes remain witness-private).
4. All other rows (in-slot padding, tail) are enabler-0 decoy rows
   contributing nothing to any relation.

### Why the existing per-slot argument carries over verbatim

- **IV / chain partition.** `is_first_block ≡ slot_starts` (preprocessed) and
  `slot_starts·(1−enabler) = 0` force every slot start to be an enabled t=0
  row with `h_in = IV`. `chain_gate = enabler·r0 − is_first_block` is 0 at
  slot starts, so no chain constraint crosses a slot boundary; within a slot
  it is the existing §10.3 chain. A malicious enabler run crossing a slot
  boundary cannot join two chains: the downstream slot restarts at IV
  regardless (its start row's `is_first_block` is pinned to 1).
- **Enabler contiguity.** The single-rise anchor generalizes:
  `(1−slot_starts)·enabler_step = 0` allows a rise only at slot starts; each
  slot start is forced enabled. Hence per slot region: at most one enabler
  run, starting at the slot start. At most one enabler drop per region ⇒ at
  most one `is_last_block` row per region.
- **`is_last_block` unchanged.** `is_last = enabler·r63·(1−enabler_next)`
  still detects "last enabled r63 row of a run". Honest traces always drop
  in-slot (≥ 64 in-slot padding rows). A prover that runs a digest slot to
  its boundary produces NO `is_last` row in that region ⇒ the slot's digest
  yield is missing ⇒ its consumer's require cannot balance ⇒ reject
  (fail-closed). Field-only slots do not depend on `is_last`.
- **Digest attribution.** Yield multiplicity `−is_last·slot_sel[s]`
  (slot_sel preprocessed) attributes the unique per-region `is_last` row to
  its slot's own digest relation. Distinct per-slot relations ⇒ no
  cross-slot digest swap is expressible.
- **Field attribution (the one NEW soundness rail).** Selectors are witness
  columns; without slot gating a prover could fire slot `s`'s selector on a
  different slot's t=15 row whose local block counter also matches (the
  counter resets at every slot start) and yield foreign bytes. Rail:
  `selector·(1−slot_sel[s]) = 0` per multi-block selector, and the legacy
  block-0 selector expression becomes `is_first_block@−15 · slot_sel[s]`.
  Covered by an adversarial test (T2).
- **Block counter.** The existing constraints (`is_first_block·b = 0`, flat
  within blocks, +1 at `chain_gate`) already make `b` = the block index
  local to the current slot's chain — no change; each multi-block exposure
  keeps its own counter column (identical values; ≤ 2 duplicate columns).
- **σ-bit fill columns.** The ungated `sched_sigma_bits =
  lower_sigma(w_bits@{−15,−2})` identities are global-cyclic over the whole
  domain (as today, incl. wraparound); the writer recomputes them over the
  merged row list — slot-agnostic.

## 2. Layout manifest

```
log_n_rows = slot_log + ceil_log2(n_slots)   (mdoc: 8 + 2 = 10)
slot region s = rows [s·2^slot_log, (s+1)·2^slot_log)
tail = rows [n_slots·2^slot_log, 2^log_n_rows)  (mdoc: 256 rows)

PREPROCESSED (consumer mode, in commit order):
  9 round-cyclic columns          (existing ids, content period-64 at log_n_rows)
  slot_starts                     NEW id "sha256_slot_starts_{n}x{slot_log}_log{L}"
                                  1 at rows s·slot_rows (s < n_slots)
  slot_sel[s], s = 0..n_slots     NEW ids "sha256_slot_sel_{s}_{n}x{slot_log}_log{L}"
                                  1 on region s's rows
  (single-slot mode keeps the existing `is_first_row` id/content — untouched)

BASE (witness): Layout::TOTAL_COLS existing columns, then per-slot
  self-contained field tails in slot order; slot s's tail reuses the
  single-instance layout verbatim: [byte cols | block counter? | selectors?]
  (FieldExposure::n_columns / selector_column_slot arithmetic unchanged,
  offset by the tail base).

  Row content: row r in region s with local block b < n_s: the existing
  write_round_row_values(witness_s, b, t) with is_first_block = (b == 0),
  is_last_block = (b == n_s−1). EVERY slot's byte columns are filled on
  every enabled t=15 row from THAT row's block words (the decomposition
  constraint is global); counters carry the local block index on every
  enabled row; selectors are one-hot on their own slot's target rows only.
  In-slot padding rows and tail rows: fresh one-block decoy witnesses per
  64-row region, public flags zeroed (existing decoy semantics per slot).

INTERACTION: ceil(L/4) QM31 cols at log_n_rows, batch-4 (LOGUP_BATCH),
  L = 66 + n_digest_slots + Σ_s field_sites(s)
  field_sites(s) = (legacy: 2·n_byte_cols(s) | multi-block:
                    2·n_byte_cols(s)·n_target_blocks(s)) + n_yields(s)
  Emission order: the existing 66 base sites (unchanged), then one digest
  yield site per digest-exposing slot in slot order, then slot s's field
  sites in slot order (each slot's inner order identical to the single
  instance).

ROW ORDERING: Pattern B (row-offset masks), natural order = global row
  index, unchanged storage mapping (Layout::row_slot).

REGISTRATION: one FrameworkComponent<Sha256Eval> (multi config set); no
  producer components (shared-tables consumer). Prover/verifier claims:
  one Sha256InteractionClaim (empty producer vectors), same as any
  shared-tables consumer.
```

## 3. Relation contracts

| Relation | Arity | Providers | Consumers |
|---|---|---|---|
| `SlotIoRelations[s].digest` (= air_core DigestBytesRelation, drawn per slot in slot order after the shared-table handshake) | 32 | merged eval, site "digest yield s": multiplicity `−is_last·slot_sel[s]` (degree 2), tuple = the row's 32 digest-byte cells | mdoc consumer holding the slot's SharedDigestRelation handle (PublicDigestBind per attribute) — handle wiring unchanged from today's per-instance handles |
| `SlotIoRelations[s].field` (= air_core FieldBytesRelation) | 3 | merged eval, one site per yield of exposure s: multiplicity `−selector_i` (multi-block; selector slot-pinned by constraint) or `−is_first_block@−15·slot_sel[s]` (legacy block-0), tuple `(field_id, byte_index, byte_cell)` | the slot's SharedFieldRelation handle consumers (revocation: MdocRevocationRangeBind + hosted ML-DSA µ-absorb; attributes: MdocWindowBind) — unchanged |
| split-pack ×8, Range_{2,4,5,16} | as today | sha_tables module (m0) | merged eval, signs/order identical to today; per-message use counts are the SUM over the three witnesses ⇒ `ShaTableMultiplicities::from_consumers` keeps the same (witness, exposure) triples — no m0 change |

Signs: consumers `+`, providers `−`, exactly as the single instance. The
digest/field draw in multi mode replaces the single digest+field draw with
n_slots (digest, field) pairs, drawn in slot order (transcript symmetric on
both sides; per-slot shape mixed in Stmt0Multi).

## 4. Degree worksheet (only NEW/changed rows; bound = log_n_rows + 2, D ≤ 5)

| Site | Expression | Degree |
|---|---|---|
| is_first_block pin | `is_first_block − slot_starts` | 1 |
| slot-start enabled | `slot_starts·(1−enabler)` | 2 |
| contiguity anchor | `(1−slot_starts)·enabler_step` | 2 |
| selector slot pin (multi-block, NEW) | `selector·(1−slot_sel[s])` | 2 |
| digest yield numerator | `is_last·slot_sel[s]` | 2 (≤ 2 numerator budget of LOGUP_BATCH=4 ✓) |
| legacy field selector numerator | `is_first_block@−15·slot_sel[s]` | 2 ✓ |
| field byte decomposition | unchanged `enabler·r15·(w − 256b1 − b0)` (fires on all slots' t=15 rows; per-slot cells decompose that row's words — sound because only slot-gated selectors feed yields/range-checks) | 3 |
| batched LogUp (batch 4, denoms deg 1, numerators ≤ 2) | unchanged | 5 |

All other constraints are unchanged from the audited single-message AIR.

## 5. Adversarial test plan

| # | Invariant | Malicious change | Expected |
|---|---|---|---|
| T1 | digest slot attribution | present slot A's digest for slot B's consumer (swap the two attribute digest requires) | claimed-sum imbalance / verify reject |
| T2 | field slot gating | fire a selector on the wrong slot's t=15 row (counter matches locally) to yield foreign bytes | constraint `selector·(1−slot_sel)` fails / reject |
| T3 | slot schedule pinned | tamper slot_starts/slot_sel preprocessed content | preprocessed fingerprint/root mismatch (I-5 guard) |
| T4 | per-slot IV reset | tamper slot 1's first-block h_in (break IV) | constraint failure / reject |
| T5 | block run crossing a slot boundary | extend slot 0's enabler run into slot 1 while keeping slot 0's digest consumer | slot 0 has no is_last row ⇒ digest yield missing ⇒ imbalance |
| T6 | revocation privacy | serialized quantum proof contains no revocation id bytes | existing privacy assert re-run green |

T1/T2/T4 at the claimed-sum/assert_constraints level in stwo-sha256; T3/T5/T6
at the mdoc level where cheap, else claimed-sum level.

## 6. Cost projection vs measured census

Baseline measured 2026-07-12 (AIR_CORE_SHAPE_DUMP, pq_perf_probe,
RAYON_NUM_THREADS=1, release): prove 7,642 ms / verify 17 ms / proof
1,277,409 B (queried 935,688, sampled 230,600, decommit 52,264, fri 55,140).

| module | preproc | trace | interaction | total |
|---|---|---|---|---|
| m4 revocation SHA (log 8) | 10 | 513 | 148 | 671 |
| m6 attr birth SHA (log 8) | 10 | 573 | 268 | 851 |
| m7 attr nat SHA (log 8)   | 10 | 562 | 244 | 816 |

Trace = 493 shared base cols + per-message field tail (20 / 80 / 69).
Interaction = ceil(L/4)·4 with L = 66 base + digest? + field sites; the 66
base sites duplicate 3× (2×68 M31 recoverable), the field sites do not.

Merged projection at log 10: preproc 13 (9 cyclic + slot_starts + 3
slot_sel) + trace 493+169 = 662 + interaction ≈ 528 ⇒ ≈ 1,203 cols.
**Recovery ≈ 1,135 cols ≈ −145 KB (at ~131 B/col incl. sampled/decommit
share) ⇒ projected proof ≈ 1.13 MB.** The S7 note's −270–290 KB assumed the
field tails/sites also dedupe — they are per-message and cannot. <1 MB is
NOT reachable by this move alone; the residual ~130 KB needs the S5 floor
items (sha_tables limb redesign / coeffs repack). Proceeding: this is still
the largest single reduction available and prerequisite to any <1 MB path.
Cells: three instances ≈ 0.60 M → merged ≈ 1.23 M (+0.6 M, ≈ +2% prove —
within the ≤8.5 s budget). Final measured delta goes to
tasks/keccak-service-design.md §S8.

**MEASURED (2026-07-12, landed):** merged module = 13 + 662 + 524 =
1,199 cols @ log 10 (projection 1,203). Proof 1,277,409 → ~1,110,700 B
(−167 KB, −13.1%); verify 17 → 15 ms; prove noise-flat (min run
7,912 ms vs 7,642 baseline, matching the +2.7% cell model under thermal
drift). Target <1 MB missed by ~110 KB, exactly per the §6 arithmetic.

## 7. Self-review (how could a prover cheat if one rail were dropped?)

- Drop `selector·(1−slot_sel)`: cross-slot byte forgery (T2 catches).
- Drop `slot_starts·(1−enabler)`: slot 1 could start disabled and re-rise
  later — but rises are only allowed AT slot starts, so the region would
  have no run at all ⇒ its digest/field yields missing ⇒ imbalance; still,
  keep the constraint: a field-only slot with zero yields consumed would
  otherwise be skippable. (Rev slot always has consumers ⇒ fail-closed
  either way; constraint kept for uniformity.)
- Drop per-slot digest relations (single shared relation): the two
  attribute digests become multiset-swappable — harmless for today's
  public-digest consumers but a footgun; per-slot relations kept (they are
  also what the existing mdoc handles expect).
- Drop `is_first_block − slot_starts`: prover could set is_first_block = 1
  mid-slot, breaking the chain into a fresh IV chain and hashing a
  different message tail — the digest would be of a forged message. This is
  the same rail the single instance has (≡ is_first_row); preprocessed
  pinning is what makes the slot schedule non-movable (I-5).
