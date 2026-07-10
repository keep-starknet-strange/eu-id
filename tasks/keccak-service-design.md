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
