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

## S6b (2026-07-12) — batch-4 family 4 (sib+decomp) + FRI rebalance (LANDED)

Family sweep after the S6 consumers (skip rule: measured gain < 30 KB):

- **Family 3 (keccak wrapper/tables) — SKIPPED by arithmetic.** keccak.rs
  boundary wrapper has 4 fracs (pairs = 8 M31 cols, batch-4 saves 4 ≈ <1 KB);
  the 9 tables_air producers are 1–2 fracs (already ≤1 pair col each);
  sponge.rs is not in the service composition.
- **Family 4 (stwo-mldsa sib + decomp) — LANDED (f6a049bb).**
  `finalize_logup()` (batch 1) → `finalize_logup_batched(4)`, bound log+2:
  decomp 23 → 6 secure logup cols (−68 M31), sib 27 → 7 (−80 M31). All
  denominators degree 1 (verified per entry) ⇒ batched constraint degree 5.
  The `[-1,0]` interaction-mask accumulators (hint_acc, Σc², sorted-pass) are
  safe at +2 — the uniform composition split already evaluated every
  component at log_size+split since S6. Writers were already LOGUP_BATCH-
  chunked; only const/bound/finalize changed. `coeffs` untouched (log+1).
  Standalone decomp/sib crate tests moved to the blowup-2 pcs_config helper.
  Measured: proof 1,810,417 → 1,732,609 B (−77.8 KB), prove 5,492 ms,
  verify 19 ms.
- **Family 5 remainder (sha256 producers) — SKIPPED by arithmetic.** All
  remaining pair-batched sha256 evals are producers with 1–5 fracs
  (single-digit column savings each, ≪100 KB total).

**FRI bake-off (82958f31)** — both pow 20 = 128-bit, measured at f6a049bb:

| schedule | prove ms | verify ms | proof B |
|---|---|---|---|
| FriConfig::new(1, 3, 36, 2) | 5,492 | 19 | 1,732,609 |
| FriConfig::new(1, 4, 27, 2) | 7,654 / 7,715 (n=2) | 18 | 1,390,409 / 1,394,537 |

Kept (1, 4, 27, 2): −340 KB (queried 1,357,400 → 1,035,920, decommit
64,808 → 53,928, fri 62,260 → 56,548) for +40% prove, verify unchanged
(proof-size-first rule, verify ≪ 100 ms bound).

### S6b final vs targets (pq_perf_probe, RAYON_NUM_THREADS=1, release)

| metric | S6 | S6b final | target | status |
|---|---|---|---|---|
| proof   | 1,810,417 B | ~1,392,000 B | <1,000,000 B | MISS by ~392 KB |
| prove   | 5,378 ms | ~7,680 ms | <1,000 ms | MISS (blowup-4 trade) |
| verify  | 18 ms | 18 ms | <100 ms | MET |

Remaining proof gap arithmetic: sampled_values 244 KB + queried 1,036 KB +
fri 57 KB + decommit 54 KB. Another −392 KB needs column-count reduction
(the S5 floor items: SHA small-load AIR / sha_tables limb redesign, coeffs
2-per-row repack) — LogUp batching is exhausted (consumers all batch-4,
producers 1-frac). Prove <1 s needs the engine FFT-extend lever plus the
same floor items; the blowup-4 schedule can be flipped back to (1,3,36,2)
whenever prove time outranks proof size.

Gates (all green, 2026-07-12, post-S6b at 82958f31): mdoc_mldsa
p256+ml-dsa 25, mdoc_mldsa quantum-safe-mdoc 19, credential_pipeline 3
(+1 ignored), stwo-keccak 31, stwo-mldsa 74 (+2 ignored), stwo-sha256 145
(+18 ignored), check-quantum-only-deps clean.

## S7 (2026-07-12) — proof-size push: query shave + column small-fry

pq_perf_probe, RAYON_NUM_THREADS=1, --release. NOTE: absolute prove_ms
drifted +25% machine-wide during this session (A/B: the UNCHANGED S6b
tree re-measured 10.2-10.4 s solo); per-slice prove deltas below are
same-session A/B, proof bytes are deterministic modulo blinding (±2 KB).

| slice | prove ms | verify ms | proof B | delta |
|---|---|---|---|---|
| S6b baseline (re-measured) | 7,592 | 18 | 1,392,493 | — |
| S7a query shave (pow 25 / 26q) | 7,902 | 17 | 1,353,541 | −38.9 KB |
| S7b prefix batch-all | ~same (A/B neutral) | 18 | 1,302,421 | −51.1 KB |
| S7c range-bind bit trim | 7,957-9,061 (median ~8.0 s) | 17 | ~1,273,900 | −28.5 KB |
| **S7 final** | **~8.0 s** | **17** | **~1,273,900** | **−118.6 KB total** |
| targets | ≤8,500 ✓ | <100 ✓ | <1,000,000 | MISS by ~274 KB |

**S7a — query shave (LANDED).** `mdoc_production_pcs_config`: pow_bits
20→25, FriConfig (1,4,27,2)→(1,4,26,2); 26·4+25 = 129 ≥ 128-bit. −38.9 KB
(queried 1,035,920→1,000,200) for +0.3 s of 2^25 blake2s grind.

**S7b — prefix producer batch-all (LANDED).** `PublicPrefixEval` (66
public bytes `tr‖00‖00` per hosted instance) was pair-batched: 33 frac
cols = 132 M31 interaction cols at 16 rows, ×3 instances = 396 cols
(census: the mystery `{4: 140}` interaction block per mldsa module).
Every denominator is an Eval CONSTANT, so `finalize_logup_batched(66)`
into ONE accumulator column keeps the batched constraint at degree ≤ 2
under the log+1 bound — no engine risk. −128 M31 cols/instance.

**S7c — MdocRevocationRangeBind bit-column trim (LANDED).** Was 376
trace cols @ log 4 (census mod 14): 40 byte cols + 320 bit cols + 16
carries. Bit-pinning is now emitted only for externally-unpinned bytes
(`revocation_range_bit_byte_indices`): id bytes are constant-pinned in
Public-digest mode (S4); id_lo/id_hi bytes are LogUp-consumed against
the revocation SHA field exposure whose producer range-checks every
exposed byte to [0,256) in-AIR (a ≥256 value has no producer tuple and
the global sum cannot balance — fail-closed); slack bytes keep bits in
all modes (no external counterpart; they carry the borrow-chain range
argument). Quantum mode: 376→184 trace cols (−192); P-256 Relation+msg
mode: 400→272 (−128). The `has_message` flag drives the bit layout and
the consume emission inside the same eval, so they cannot desync.

**S7-merge (three log-8 SHA consumers → one instance) — STOPPED by the
400-line rule; arithmetic report.** The census puts the three quantum
SHA consumers (revocation m4: 671 cols, attributes m6/m7: 851 + 816
cols) at 2,338 committed cols ≈ 306 KB of proof for ≤768 rows of load;
a log-10 merged instance would save ~2.0-2.2k cols ≈ −270-290 KB.
Reading stwo-sha256 kills the "mostly mdoc-side" hope — the AIR is
single-message by construction:
- `is_first_block ≡ is_first_row` (constraints.rs:250, preprocessed
  selector) — one IV reset per component; a merged instance needs a
  slot-schedule preprocessed family (new ids + dedup namespace, since
  the current is_first_row content is log-dependent but id-shared
  across instances).
- `is_last_block = enabler·r63·(1−enabler_next)` + single-rise
  contiguity anchor `enabler_step` (gated on is_first_row) — per-slot
  re-rise and per-slot last-block detection need new gates.
- ONE digest handle (relation, final-block gate) and ONE field-exposure
  relation — per-message digests to DISTINCT SharedDigestRelations and
  multi-relation field yields are component API + interaction rewrites.
- trace generation (SIMD + scalar paths + zk decoy padding) assumes one
  contiguous block run; per-slot generation is a rewrite of both paths.
Estimate: 600-1,100 lines in stwo-sha256 (witness/trace/constraints/
interaction/air/preprocessed + Sha256Verifier mirror) + ~300 in mdoc.rs
(both paths) + a wire-format break (module count changes). This is the
only remaining item big enough to reach <1 MB: post-S7 floor arithmetic
is queried ~921 KB + sampled ~231 KB + fri/decommit ~105 KB at 8.6k
cols; −274 KB more needs the SHA merge (−~280 KB) or the S5 floor items
(sha_tables limb redesign, coeffs 2/row repack).

Remaining census small-fry (all < 30 KB each, skipped by the S6b rule):
window_bind 136 inter cols (batch-4 ≈ −9 KB), keccak sponge pad_mask
136-col preprocessed ×2 jobs (fold to 2 cols ≈ −17 KB, touches pad10*1
constraints), bridges/sinks pairs (≈ −6 KB/instance).

Gates (all green, 2026-07-12, post-S7): mdoc_mldsa p256+ml-dsa 25,
mdoc_mldsa quantum-safe-mdoc 19, credential_pipeline 3 (+1 ignored),
stwo-mldsa full suite, check-quantum-only-deps clean. (e2e_soundness is
a p256-only test target — it never compiled under quantum-safe-mdoc and
is not a quantum gate.)

### Post-S7 FRI frontier (pq_perf_probe, RAYON_NUM_THREADS=1, same session)

| schedule | prove ms | verify ms | proof B |
|---|---|---|---|
| (1, 4, 26, 2) pow 25 — production | 7,957-9,061 (median ~8.0 s) | 17 | ~1,273,900 |
| (1, 3, 36, 2) pow 20 — buy-back   | 5,385 / 5,716 | 18 | ~1,629,900 |

Buying prove back to ~5.4 s costs +356 KB of proof. Both rows share the
post-S7 column count; flip whenever prove time outranks proof size.

## S8 (2026-07-12) — three log-8 SHA consumers → ONE multi-slot instance (LANDED)

The quantum composition's remaining SHA consumers (revocation m4 671 cols +
attributes m6/m7 851/816 cols, 2,338 total) merge into ONE slot-scheduled
`Sha256MultiProver` instance at log 10 (3 uniform 256-row slot regions,
schedule preprocessed-pinned; per-slot digest/field relations map 1:1 onto
the existing mdoc handles, consumer modules unchanged). Design + soundness
rails + adversarial matrix: tasks/sha-multimessage-design.md. P-256 mode
untouched (separate prover/verifier pair; `Sha256Eval.multi = None` is the
byte-identical legacy path). Wire format: `merged_sha_*` claim fields,
biconditional with the legacy per-instance fields (fail-closed both ways).

Measured merged module (AIR_CORE_SHAPE_DUMP): 13 preproc + 662 trace + 524
interaction = **1,199 cols @ log 10** (projection was 1,203) ⇒ −1,139
committed cols. Cells 22.85M → 23.48M (+0.63M: 768 rows of load in a
1,024-row domain — proof size is column-bound, not row-bound).

pq_perf_probe, RAYON_NUM_THREADS=1, --release, production (1,4,26,2)/pow25:

| point | prove ms | verify ms | proof B |
|---|---|---|---|
| S7 baseline (re-measured same session) | 7,642 | 17 | 1,277,409 |
| **S8 merged** (n=3) | 7,912 / 9,453 / 11,185 (min ≈ baseline +3.5%, thermal drift dominates) | 15 | **1,109,688 / 1,110,312 / 1,112,152** |
| targets | ≤8,500 ~✓ (min-run) | <100 ✓ | <1,000,000 **MISS by ~110 KB** |

Delta: **proof −167 KB (−13.1%)** (queried 935,688→810,360, sampled
230,600→190,720, decommit −0.9 KB, fri −1.5 KB); verify 17→15 ms; prove
noise-flat (cell-model prediction +2.7%; the 9.5-11.2 s runs are the same
machine-wide thermal drift S7 recorded).

**Why the S7 estimate (−270–290 KB) was optimistic:** only the duplicated
BASE surface dedupes (2×493 trace cols + 2×17 base-site interaction QM31).
The per-message field tails (20/80/69 cols) and per-slot field/digest
interaction sites (~456 M31 cols) are witness-carrying and cannot merge.
<1 MB therefore still needs ~110 KB from the S5 floor items (sha_tables
limb redesign ≈ −88 cols won't do it alone; coeffs 2/row repack or an
8-bit range table for field bytes are the candidates).

### Post-S8 FRI frontier (pq_perf_probe, RAYON_NUM_THREADS=1, same session)

| schedule | prove ms | verify ms | proof B |
|---|---|---|---|
| (1, 4, 26, 2) pow 25 — production | ~7,900+ (thermal-noisy) | 15 | ~1,110,700 |
| (1, 3, 36, 2) pow 20 — buy-back   | 5,755 / 5,984 | 17 | 1,419,536 / 1,423,024 |

Gates (all green, 2026-07-12, post-S8): stwo-sha256 152 (+2 new multi_slot,
+5 multi negatives; +19 ignored incl. the multi composition round trip, run
once explicitly), mdoc_mldsa quantum-safe-mdoc 19/19 (incl. revocation e2e,
G6 privacy assert, wire round-trip), mdoc_mldsa p256+ml-dsa 25/25,
credential_pipeline 3 (+1 ignored), mdoc_support 46, compose_p256_sha
default suite green (3 of its `--ignored` WO-1.x diagnostics assert
two-prove BYTE IDENTITY and fail by design since Q-015 random decoy
padding — pre-existing, not S8), check-quantum-only-deps clean.

## S9 (2026-07-12) — close the last ~110 KB: census, pricing, HONEST STOP

Goal: proof < 1,000,000 B (from 1,109,272 B), verify < 100 ms, prove ≤ ~8.5 s
min-of-3. **Result: NOT REACHED. No sanctioned move closes the gap inside the
soundness + prove-budget rails.** Baseline held; nothing shipped.

### Fresh census (AIR_CORE_SHAPE_DUMP, pq_perf_probe, RAYON_NUM_THREADS=1)

Baseline proof 1,109,272 B = queried 810,360 (73%) + sampled 190,720 (17%) +
fri 53,316 + decommit 51,240 + meta/commitments/pow 3,636. Prove 8,232 ms
(min), verify 14 ms.

The proof is **column-bound**: queried_values = n_queries(26) × committed
M31 columns × 4 B; sampled_values ∝ columns. Decommit is per-tree Merkle
paths (depth ∝ log_size), NOT per-column; fri is per-layer. So the only
lever that moves the two dominant terms is **fewer committed columns** (or
fewer queries). Established price (S8, −167 KB / −1,139 cols): **≈145 B per
committed M31 column** (queried ≈110 B/col + sampled ≈35 B/col).

Committed columns per module (all trees; total **7,290**):

| module | cols | identity | status |
|---|---|---|---|
| 1 | **4,014** | mldsa keccak service (sponge_v + keccak + round + 9 tables) | protocol-pinned (45 SHAKE perms, hard floor); interaction already batch-4 on the two big components (sponge_v 684 + keccak_round 908 of 1,628) |
| 4 | 1,199 | merged multi-slot SHA consumer (S8) | already `finalize_logup_batched(4)`; field/digest sites witness-carrying |
| 5 | 436 | hosted ML-DSA (revocation) | contains coeffs component — **NEVER touch** |
| 2, 3 | 432 ea | hosted ML-DSA (issuer / device) | contains coeffs component — **NEVER touch** |
| 8 | 244 | digest/window bind (log 9) | functional |
| 12 | 233 | predicate/range (log 4) | functional |
| 9 | 119 | bind (mixed log) | functional |
| 0 | 88 | shared SHA tables (log 17 preproc) | S5 limb-redesign target (≈−88 cols) |
| 6, 7 | 37 ea | small binds (log 9) | functional |
| 10 | 19 | small | functional |
| 11 | 0 | (empty) | — |

**To reach <1 MB: need −109,272 B ≈ −754 committed columns** at 145 B/col.

### Every sanctioned S9 move, priced against the fresh census

1. **8-bit range table for SHA field-byte range sites** — NOT AVAILABLE.
   The SHA AIR has only Range2/4/5/16 (no `[0,2⁸)` provider);
   `field_exposure.rs` pins each exposed byte with **two** Range16 lookups
   (`b`, `b+OFFSET`). There is no existing 8-bit table to *reuse*, and a new
   single-purpose table is forbidden (M-5) — it would add a preprocessed
   column + multiplicity + interaction for the handful of exposed bytes, net
   ≈ break-even. The keccak service's spread tables are a different relation
   set in a different module; wiring the SHA consumer to draw a keccak table
   is a cross-module soundness change for < 15 KB. **Rejected.**

2. **Remaining pair-batched evals → batch-4** — LARGELY EXHAUSTED.
   Census: the two large keccak-service interaction components (`sponge_v`
   684 cols, `keccak_round` 908 cols) are ALREADY batch-4 (bound log+2). Only
   `keccak` (permutation) + `tables_air` (9 tables) still finalize in pairs,
   ≈ 36 interaction cols combined ⇒ batch-4 saves ≈ 18 cols ≈ **−2.6 KB**, and
   requires bumping their bound log+1 → log+2 (more composition-domain prove
   work). Marginal, adds risk for ~2 KB. **Rejected** (not worth the bound bump).

3. **Query / pow micro-tuning** — OUT OF BUDGET (measured).
   26→25 queries needs pow 25→28 to hold 25·4+28 = 128-bit. Measured
   pow-28 single-thread: **prove 32,413 / 37,003 ms** (grind ≈ +24 s),
   proof 1,076,444 B (−33 KB, still >1 MB). The blake2s grind at 2^28 is
   ~24 s single-thread — catastrophically over the 8.5 s budget for a −33 KB
   gain. **Rejected.** (Reaching −110 KB via queries needs 3 fewer queries ⇒
   pow 37 ⇒ minutes of grind — infeasible.)

4. **Misc small-fry** — sub-threshold. sha_tables limb redesign ≈ −88 cols ≈
   **−12.8 KB** (non-trivial, touches protocol-pinned SHA table structure,
   S5 hard-floor item); coeffs 2/row repack is forbidden AND net-neutral for
   a column-bound proof (doubles per-row cols, halves rows). No dead/duplicate
   columns found in the functional small modules.

### Residual arithmetic (what remains, what each costs)

Best-case sum of every *clean* item above: keccak pairs→4 (−18) + sha_tables
limb redesign (−88) = **−106 cols ≈ −15.4 KB** → 1,093,900 B. Still **~94 KB
(≈650 cols) over target.** The remaining 754 cols only exist in:
(a) the keccak service (4,014 cols, 45 protocol-pinned SHAKE perms — hard
floor, tasks §S5); (b) the hosted ML-DSA coeffs/verify modules (~1,300 cols —
coeffs forbidden); (c) the merged SHA consumer (1,199 cols — already batch-4,
sites witness-carrying). Cutting 754 cols from these requires a **structural**
change (keccak sha_tables limb redesign to shrink the log-17 preprocessed +
per-perm columns, or an engine-level column-packing of the coeffs component),
each explicitly out of scope / forbidden for S9 small-fry.

**Honest conclusion: <1 MB is not reachable with the S9 small-fry list.** The
proof floor at the current architecture is ≈1.09 MB. Closing to <1 MB needs
the S5 SHA-table limb redesign (est. −12–15 KB) *plus* a keccak per-perm
column reduction — a structural project, not an S9 move. Baseline unchanged
(1,109,272 B / 8,232 ms / 14 ms); production FRI (1,4,26,2)/pow25 retained.

### FRI frontiers (pq_perf_probe, RAYON_NUM_THREADS=1, S9 session)

| schedule | prove ms (min) | verify ms | proof B |
|---|---|---|---|
| (1, 4, 26, 2) pow 25 — production (retained) | 8,232 | 14 | 1,109,272 |
| (1, 4, 25, 2) pow 28 — query shave (rejected) | 32,413 | 15 | 1,076,444 |
| (1, 3, 36, 2) pow 20 — buy-back (S8) | 5,755 | 17 | 1,419,536 |

No code changed; existing gates remain as recorded post-S8.

## Q1/Q2 (2026-07-13) — quantum branch split + direct revocation provider

The dedicated `feat/quantum-safe` branch now defaults to the full ML-DSA product and removes the
legacy identity/nonce/coprocessor API, SDK/FFI ABI, mobile surfaces, benches, and classical tests.
P-256/ec-coprocessor crates are excluded from the workspace and the locked whole-workspace
dependency gate is clean. The final internal `eu-id-prover` scheme-cfg collapse remains follow-up;
the default product graph is already quantum-only.

Revocation no longer enters the merged SHA consumer. `MdocRevocationRangeBind`, which already owns
the constrained `id_lo`/`id_hi` witness and public epoch, now draws the shared field relation and
provides `LE64(id_lo)||LE64(id_hi)||LE32(epoch)` directly under `HOSTED_MSG_FIELD_ID` with provider
sign. All 16 private bound bytes regain local 8-bit decomposition, so removing SHA does not remove
their range proof. The component is ordered before the hosted revocation ML-DSA instance on both
prove and verify; a focused bound-byte/message mismatch negative and the full privacy/e2e rail pass.

Shape/metric result (`AIR_CORE_SHAPE_DUMP=1`, release, `RAYON_NUM_THREADS=1`):

| metric | S9 | Q2 | delta |
|---|---:|---:|---:|
| merged SHA columns | 1,199 @ log 10 | 1,098 @ log 9 | −101 |
| total committed columns | 7,290 | 7,317 | +27 |
| proof | 1,109,272 B | 1,113,700 B | +4,428 B |
| prove | 8,232 ms | 8,192 ms | noise-flat |
| verify | 14 ms | 16 ms | noise-flat |

The +27-column total is exact: removing the revocation SHA slot saves 101 columns; restoring local
bit pinning for 16 private bytes adds 128. This stage is retained because it deletes a legacy hash
work class and makes Q3's input honestly attribute-only, but it is not claimed as a performance win.
The next design must recover this ~4 KB regression while replacing the P-256-era fixed SHA tables.

## S10. Q4 GKR-offload pricing (recorded — see quantum-safe-branch-plan.md §8.2)

The one lever that reaches <1 MB: offload the `keccak_round` LogUp (908 base
interaction cols @ log 11, the biggest single fraction set in the 1,628-col m1
interaction tree) from committed tree-2 columns into a LogUp-GKR proof, keeping
only the cheap MLE-eval tie-back columns committed.

Column arithmetic PASSES the >80 KB gate: `(908 − ~30 tie-back) × 145 B` minus a
few-KB `GkrBatchProof` blob ≈ **+120 KB net** — clears the −83 KB proof gap
alone. `keccak_round`'s relations (`KeccakState`/xor3/andnot/split) are
service-internal, so the cross-module `HashIo` balance stays columnar (tighter
soundness surface than offloading sponge_v).

STOP for now: integration is structural, not arithmetic — (1) no `GkrBatchProof`
transport in the proof wire (`air_core::prove`→`StarkProof`;
`verify_post_interaction(channel)` cannot receive it; needs an
`MdocCircuitProof` field + serialization); (2) `MleEvalProverComponent` is a
fork example (`crates/examples/src/xor/gkr_lookups/mle_eval.rs`, dead-code, 1,308
lines) needing productionization + a bespoke `MleCoeffColumnOracle`; (3) the GKR
output claim must bind the same drawn relations and equal `round_claimed_sum`.
Dedicated multi-checkpoint WO, gated behind adversarial negatives.

coeffs 2/row repack (§S9 line ~566) reconfirmed **net-neutral** by independent
Q4 derivation: committed cells = columns × 2^log; same-row lookup uses need
distinct fraction columns, so 2/row doubles fraction/base/preproc columns while
halving rows ⇒ cells invariant, columns 132→~252/instance, proof WORSE (~+50 KB
over 3 instances). No prove win beyond a small `n·log n` edge. Not pursued.
