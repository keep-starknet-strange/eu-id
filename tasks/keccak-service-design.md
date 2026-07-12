# Keccak Service Module — Design (PQ perf campaign S1)

Goal: full-PQ mdoc at prove <1s / verify <100ms / proof <1MB (single-thread).
Baseline (2026-07-10): prove 72.7s, verify 372.7ms, proof 34,424,854 B.

## Measured whale (layout_probe, ONE instance, 2KB message)

- trace 20,821 cols (14,599 @ log4), interaction 26,520 cols (24,192 @ log4),
  total 7.54M cells but ~47k COLUMNS → ×3 instances ≈ 140k columns.
- Cause: sponge AIR is HORIZONTAL — one 16-row packed row, one column per
  absorb/state/squeeze byte ("ponytail: one instance ⇒ single packed row").
  Column count ∝ message bytes. Proof size = 54 queries × columns; prove time
  = per-column LDE/Merkle constant costs; verify = Merkle path flood.

## Moves (performance-derivation playbook)

- M-4 rotate sponge wide→tall: one row per PERMUTATION, constant width.
- M-1/M-2 dedup: ONE keccak side (sponges + keccak + round + tables) for the
  whole proof, all instances, right-sized rows.
- M-6: FRI schedule rebalance + zstd wire (S2), static preprocessed caches (S3).

## S1 architecture

New module in stwo-keccak: `service::KeccakService` (Air + AirProver),
hosted by the composition exactly once. It owns:

1. All sponge jobs of the proof (mu/ct/sib × instances), one rotated sponge
   component (or one per job initially — measure), rows = permutations.
2. The keccak state component, round component, and 9 tables — once.
3. The relations: `KeccakRelations` drawn by the service, published to
   consumer modules via a `SharedKeccakRelations` handle (same pattern as
   `SharedFieldRelation`); consumers (mldsa bridges/prefix/sinks/decomp/sib)
   emit HashIo uses/yields against it.

Stream-id discipline: with ONE shared HashIo relation, stream ids must be
globally unique → per-instance base offset: `stream_id = role_base + chain`,
role_base ∈ {issuer=0x100, device=0x200, revocation=0x300} × plus the sha256
field ids are a DIFFERENT relation (FieldBytesRelation) — no interaction.
Perm ids: one global PermIdPlan over the concatenated job list.

## Rotated sponge — layout manifest (per job; Pattern B chaining)

```
log_size = ceil_pow2(n_perms_total_of_job)  [min LOG_N_LANES]
Row r = permutation r of the job (absorb perms then squeeze perms).

PREPROCESSED (schedule; per job, witness-INDEPENDENT given shape):
  is_active        1 col   row < n_perms
  is_first         1 col   row == 0
  is_absorb        1 col   absorb perm rows (consume a block)
  is_squeeze_out   1 col   rows whose PRE-state rate is squeezed out
  perm_id          1 col   global perm id (base + r)
  io_pos_base      1 col   byte position base for HashIo (r*136 offsets)
  pad_mask[136]    136 cols pad10*1 constant per rate byte of the LAST absorb
                   row (0 for message bytes, pad constant else)  — OR fold
                   into 2 cols (pad_pos + boundary flags) if constraints allow;
                   start with 136, measure, then minimize.

BASE (witness):
  block_byte[136]     byte form of the absorbed block   (absorb rows only)
  block_spread[136]   spread form                        (conv-checked)
  new_rate[136]       xor3(prev_post_rate, block_spread) (absorb rows > first)
  post[200]           post-permutation spread state
  squeeze_byte[136]   byte form of squeezed rate         (squeeze rows only)
  TOTAL ≈ 744 base cols
```

Cross-row: Pattern B masks `[-1, 0]` on `post` (prev row's post = chaining
state). First row: pre-state rate = block0_spread, capacity = 0.

Relation emissions per row (gated by schedule flags):
- conv use per block byte (absorb) and per squeeze byte (squeeze): ≤136/row
- xor3 use per rate byte (absorb rows after the job's first): ≤136/row
- HashIo: consume message bytes (absorb, −), yield squeeze bytes (+): ≤136/row
- KeccakState: yield IN tuple (perm_id, 0, pre_state[200]) where
  pre_state = [new_rate or block0_spread or prev_post rate | prev_post capacity
  or 0]; require OUT (perm_id, 1, post[200]): 2/row (wide tuples PRESERVED —
  keccak.rs/round.rs/tables unchanged in S1)
Interaction ≈ (136+136+136+2)/2 × 4 ≈ 820 cols.

Column budget: ~1,600 cols × rows≈128 (70 perms padded) for the ENTIRE
proof's sponge work (vs ~70,000 today). Cells ≈ 0.2M. Round/keccak/tables
unchanged in S1: ~3.5k cols, ~6.5M cells (S3 target).

## Constraints (degree worksheet)

| Site | Expression | Degree | Bound |
|---|---|---|---|
| enabler/flags boolean | f(1−f) | 2 | log+1 ✓ (preprocessed flags need NO boolean constraint — preprocessed is trusted) |
| pad bytes | is_last_absorb × (block_byte[j] − pad_const[j]) | 2 (flag preprocessed → deg 1) | ✓ |
| first-row pre-state | is_first × (pre_rate[j] − block0_spread[j]) — folded into the IN tuple construction, no extra constraint | — | ✓ |
| logup (pairs) | batch 2 | +1 | log+1 ✓ |

All schedule flags/pad constants are PREPROCESSED → most constraints are
degree ≤2 with preprocessed gates. The IN tuple mixes prev-row masks
(degree 1 each) — RelationEntry values, fine.

Soundness invariants:
- I-1: every base cell is either conv/xor3-table-constrained (spreads,
  bytes), state-relation-constrained (post via keccak component), or
  HashIo-bound (message bytes). Padding rows gated by is_active.
- I-2: signs preserved EXACTLY from the horizontal design (conv/xor3 use +,
  HashIo consume − / yield +, state yield + IN / require − OUT as today).
- I-3: bytes/spreads range-enforced by conv table membership (uses), as today.
- I-4: message bytes bound via HashIo against bridge/prefix producers
  (unchanged contract).
- I-5: schedule preprocessed ids encode (job list shape, perm bases, message
  lens) — id = hash-of-shape string or explicit params in id; fingerprint
  guard already enforced by air-core.

## Consumer-side changes

- stwo-mldsa `statement.rs`: drop sponges/keccak/round/tables from the
  module's component set and claims; shapes move to a `KeccakJobs` spec the
  host passes to the service; bridges/prefix/sinks/decomp/sib take the
  shared relations handle. mix_public: job shapes mixed by the SERVICE once
  (log_size, stream ids, perm bases); instance mixes only its message-shape
  contribution as today.
- mdoc: compose `[sha_tables, keccak_service, issuer_sha, issuer_mldsa, ...]`;
  service constructed from the 3 instances' job shapes (public), witness =
  their sponge byte streams.
- Claims plumbing: service contributes its own claimed_sums vector; per-
  instance mldsa claims shrink (no sponge/keccak/round/table slots).

## Adversarial tests (S1 gate)

| Invariant | Test |
|---|---|
| I-2 xor path | tamper one new_rate spread byte → logup unbalanced |
| I-2 state chain | tamper one post byte → keccak OUT require fails |
| I-4 msg binding | producer yields different byte → reject (existing hosted test, re-run) |
| pad | non-canonical pad byte in last block → constraint fail |
| cross-instance | device claim replay against revocation slot → reject (existing) |
| shape | wrong sib_stream_len → shape gate / logup reject (existing) |

## Stage gates (measure after each; iron rule)

| Stage | Expected | Gate |
|---|---|---|
| S1 service+rotation | cols 140k→~12k; prove 72.7s→~4-6s; size 34.4MB→~3MB; verify →~150ms | full mdoc_mldsa suite + stwo-mldsa suite green |
| S2 FRI/zstd/round-batch | size <1MB | 128-bit budget preserved (queries×log_blowup+pow=128) |
| S3 round cells + caches | prove <1s | suites green |
| S4 verify path | verify <100ms cold | suites green |

S1 MEASURED (2026-07-10, mdoc S1 wiring; full-PQ issuer+device+revocation,
RAYON_NUM_THREADS=1, --release, production PCS): prove 77.14s (baseline 72.7s —
flat: prove is not column-constant-bound; S3 round cells is the prove lever),
verify 275.8ms (was 372.7ms, −26%), proof 14,891,983 B (was 34,424,854 B,
−57%). Gates: mdoc_mldsa 24/24 (p256+ml-dsa) + 18/18 (quantum-only) green,
credential_pipeline green, quantum-only dep tree clean.

S3a MEASURED (2026-07-10, keccak wrapper rotation — one row per round
boundary, 25 rows/perm, 5,102 → 209 committed cols): prove 21.0s (S2-era
baseline 20.6s, flat), verify 87ms (was 99ms), proof 13,674,271 B (was
14,890,143 B, −8.2%). Full stwo-keccak + stwo-mldsa + mdoc_mldsa suites green.

S3b DEAD END (2026-07-10, logup batching sweep): batch-4 finalize needs
max_constraint_log_degree_bound = log+2, and this stwo fork's lifted
composition REQUIRES bound == log_size + 1 EXACTLY for every framework
component — control experiment (UNCHANGED pair batching, bound log+2 only,
Sha256Eval) fails prove with the OODS ConstraintsNotSatisfied; keccak_round
at +2 under blowup-1 panics "polynomial's coefficients are not stored"
(EvaluationMode::ExtendToEvalDomain needs stored coefficients — only the
P256 lifting path enables that). The M4 trap is therefore GENERIC, not
Horner-specific. Max legal batch at deg ≤ 3 is pairs — already used
everywhere. Wider batching requires engine work (fix/enable the
ExtendToEvalDomain path), not component work.

S3 FRI EXPERIMENT (2026-07-10, log_blowup 3 + 36 queries = 128-bit,
REVERTED): proof 9,733,783 B (−29%) but prove 31.8s (+51%: tree commits
double with the extra LDE) and verify 139ms — breaches the <100ms verify
bound. Production config stays (log_blowup 2, 54 queries, pow 20).
[SUPERSEDED by S4: after the S4 producer removals the schedule flipped —
fab03a14 landed log_blowup 3 / 36q / pow 20 as production; S5 baseline
below is measured on it.]

## S5 (2026-07-12) — right-sizing pass; measured table

pq_perf_probe, RAYON_NUM_THREADS=1, --release, single prove+verify:

| point | prove ms (median) | verify ms | proof B | cells |
|---|---|---|---|---|
| S5 baseline (fab03a14) | 5,031 (n=3) | 20 | 2,203,217 | 28.5M |
| S5c SIB right-size     | 4,911 (n=8) | 20–32 | ~2,201,000 | 26.9M |
| targets                | <1,000 | <100 ✓ | <1,000,000 | — |

Run-to-run prove noise is ±3% (4,833–5,091 post-S5c); the deterministic
S5c measure is the cell count (−1.6M, −5.7%). Gates (all green,
2026-07-12): mdoc_mldsa p256+ml-dsa 25, mdoc_mldsa quantum-safe-mdoc 19,
stwo-keccak 31, stwo-mldsa 74, credential_pipeline 3 (+1 ignored),
check-quantum-only-deps clean.

Phase split at baseline (AIR_CORE_PROVE_TIMING): tree0 705ms
(write+commit), tree1 844ms, tree2 1,611ms, stark 1,314ms, witness-gen
~0.5s outside air-core.

**S5c — LANDED.** `sample_in_ball` squeezed a flat generous 8+8·N=2,056 B;
the sib component is sized by that FULL squeeze length. On-demand
block-wise squeeze (136 B) drops sib_log_size 12→10 per instance
(−1.6M cells, −5.7%). prove −2.4%, proof flat. Keccak jobs were already
sized by the consumed `sib_stream_len` — no sponge change.

**S5b — PARKED (attribution measured).** m0 sha_tables = 88 cols /
9.31M cells (35% of post-S5c cells): 42 preprocessed @ log 17 (4 round
split-pack ×6 cols + 4 σ split-pack ×4 + Range_16 ×2, all Class-D doubled
2^16→2^17) + 9 multiplicity @ 17 + 20 interaction @ 17. Attributable
prove ≈ 1.4s of 5.0s (78% of tree0 = ~550ms; ~20% of tree1/tree2 =
~470ms; ~33% cell share of stark = ~430ms). Cannot shrink without a
consumer redesign: the split-pack key domain is the FULL 16-bit half —
16-bit halves are baked into `partitions::s_mask` (masks over 32-bit
words), the (lo,hi) limb trace layout, and every consumer constraint;
the limb→packed-groups map is bit extraction (non-linear), so no
in-constraint replacement. A 2^12–14 variant = multi-day stwo-sha256
redesign (P-256 mode must keep the big tables regardless). In-place
dedupe of the 8 identical key + 8 is_dummy preprocessed cols was
arithmetic-rejected: −14×2^17 = −1.83M cells ≈ −200ms (4%), <5% bar.

**S5a — PARKED (at arithmetic floor).** keccak_round lookups/row = 898:
80 θ-parity (2 xor3/C-byte, ceil((5−1)/2) minimal) + 40 C-rot split +
200 θ-apply + 176 ρ split + 200 andnot + 200 χ-close + 2 chain. Under
base-4 spread (3-operand xor cap), 2^16 dense tables, deg ≤ 2, pairs-only
batching: θ-apply/andnot/χ-close are each a forced non-linear op per
state byte (3×200 floor). Rejected by arithmetic: (i) fusing χ-close's
free 3rd slot (24/25 lanes) with next round's θ-apply — 4 xor operands
overflow the base-4 digit (max 4 > 3); base-8 spread ⇒ 2^24 tables ≫
savings; (ii) 2 rounds/row — same cells, doubles cols, worse proof;
(iii) batch-4 logup would halve the 1,796 interaction cols but is the
S3b engine dead end (bound == log_size+1). Rows: n_perms_total = 45
(measured, KECCAK_PERMS_DUMP=1) → 45×24 = 1,080 rounds → log 11; log 10
needs ≤ 42 perms (round) / ≤ 40 (wrapper). Load is protocol-pinned per
instance: c̃ = 7 perms (FIPS 204 832-B absorb), µ = 7 (mdoc SigStructure
~850 B), SIB = 1 (post-S5c). Shaving ≥ 5 perms would halve the m1 round
block (−3.2M cells) — requires changing what is hashed, not the AIR.

**Hard-floor arithmetic vs targets (post-S5c: 4,868ms / 2.20MB / ~20ms):**
- Proof: queried_values = 11.66k cols × 36q × 4B ≈ 1.68MB + sampled
  0.31MB + decommits/FRI 0.13MB. Interaction cols ≈ 6.4k of 11.7k; the
  single biggest unlock is engine-side logup batching ≥ 4 (−3.2k cols ≈
  −460KB). Next: merge the three log-8 SHA consumers m4/m6/m7 (~2.99k
  cols total ≈ 430KB of proof for ≤ 768 rows of load) into one hosted
  component (−~290KB), and/or blowup-4/27q (×0.75 queried). All three
  together ≈ 0.9–1.0MB — batching alone does not reach <1MB.
- Prove: 26.9M cells × blowup-8 LDE + merkle ≈ 2.9s commits + 1.3s stark
  + 0.5s witness. Irreducible under current component designs: m0 9.3M
  (SHA-table redesign), m1 6.4M round block (protocol-pinned 45 perms),
  3× coeffs @ log 14 ≈ 7.1M (active 9,204 rows of 16,384 — off-limits
  this stage; 2-coeff/row packing would fit log 13 and save ~2.4M cells).
  Even deleting m0 entirely leaves ~17.6M cells ≈ ~3.2s single-thread.
  <1s single-thread needs SHA-table redesign + coeffs repack + engine
  batching, or multi-thread proving.
- Verify: 20–29ms, comfortably under the 100ms bound at 36q/blowup-3.

## S6 (2026-07-12) — LogUp batch-4 via engine unlock (LANDED)

The S3b engine constraint is FIXED: stwo fork rev `8c998390` generalizes the
composition split to `K = max(bound - log_size)` (was hardcoded 1), so
FrameworkComponents may declare `bound = log_size + 2` (D≤5 ⇒ LogUp batch 4).
Constraint evaluation reuses committed evals whenever `K ≤ log_blowup`
(production blowup 3 ⇒ no stored coefficients needed). Degree accounting:
stwo repo `.claude/skills/paper-implementation-divergence-log.md`
DIVERGENCE-004. Engine repro/regression: `test_state_machine_raised_degree_bound_*`.

Switched to batch 4 at `bound = log+2`: keccak_round (898 fracs, interaction
cols 1796 → 900), sponge_v (684 fracs, 1368 → 684), Sha256Eval (66-67 fracs,
33 → 17 secure cols). Producers left on pairs (1 frac each — no benefit);
stwo-mldsa `coeffs` untouched at log+1 by design (Horner accumulator).
Crate tests that prove at `PcsConfig::default()` (blowup 1) moved to a
blowup-2 pcs_config() helper (stwo-keccak tests, stwo-mldsa composed/hosted) —
weaker than production's blowup 3.

pq_perf_probe, RAYON_NUM_THREADS=1, --release, n=4:

| point | prove ms (median) | verify ms | proof B |
|---|---|---|---|
| S5c baseline | 4,911 (n=8) | 20–32 | ~2,201,000 |
| S6 batch-4   | 5,378 (5,338–5,434) | 18 | 1,810,481 |
| targets      | <1,000 | <100 ✓ | <1,000,000 |

Proof −390 KB (−17.8%); sampled_values 255,080 B, queried_values 1,424,888 B.
(Spec estimate was −460 KB assuming all interaction cols halve; consumers-only
scope lands −390 KB. The ~1.75 MB acceptance point is missed by ~60 KB.)
Phase split (AIR_CORE_PROVE_TIMING): tree2 1,611 → 1,337 ms (down as
predicted), tree1 844 → 771 ms, tree0 705 → 665 ms, BUT
stark-prove 1,314 → 2,026 ms: uniform-K lifting makes EVERY component
(including the huge coeffs Horner) evaluate constraints on a 4× trace-size
domain instead of 2×. Net prove +9.5% (4,911 → 5,378 ms).

Follow-up levers (not done): (a) FFT-extend low-excess components' quotient
columns (interpolate at n+1, evaluate at n+2) instead of re-evaluating
constraints on the doubled domain — recovers most of the +712 ms stark cost,
engine-side change; (b) batch-4 the remaining pair-batched consumers
(mdoc SHA windows, bridges) for the residual ~-70 KB toward the -460 KB
estimate; (c) the S5 floor items (SHA small-load AIR, coeffs repack).

Gates (all green, 2026-07-12, post-S6): mdoc_mldsa p256+ml-dsa 25,
mdoc_mldsa quantum-safe-mdoc 19 (--no-default-features), stwo-keccak 31,
stwo-mldsa 74, stwo-sha256 145, credential_pipeline 3 (+1 ignored),
check-quantum-only-deps clean.
