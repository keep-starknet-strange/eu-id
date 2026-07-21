# SHA-256 lookup-table limb redesign — design spike

Branch `feat/sha-limb-redesign` @ `cddef7fd` (== `build/release-lto`, pinned upstream stwo, no local patches).
Design spike only — **no production code changed**. Companion: `tasks/sha-limb-redesign-partitions.txt`.

**Verdict up front: BUILD (w = 8).** The committed SHA table mass shrinks
9,306,656 → 61,472 cells (−99.3%); the net SHA subsystem (tables + 4 message
components) shrinks ~82%; projected prove-time win is **39–51%**, far above the
15% go/no-go bar. But see §5 — the same analysis shows the split-pack tables may
be **entirely removable** on this branch, which dominates w=8 and should be
checked first.

---

## 0. Current-scheme census (reconciled to the measured numbers)

### 0.1 What is actually committed in the mdoc proof (correction to the brief)

The brief's inventory ("8 Σ/σ decode tables, 8 split-pack, 1 xor_8, 1 Maj/Ch")
describes the **standalone** `stark.rs` path (23 components). The **mdoc / shared
path this spike optimises does NOT commit the decode / xor_8 / Maj-Ch tables at
all.** On this branch `Sha256Eval` evaluates Σ0/Σ1/σ0/σ1/Maj/Ch from full
32-bit-plane boolean columns (`constrain_boolean_bits`, `big_sigma0_expr_bits`,
`maj_expr_bits`, `ch_expr_bits` in `constraints.rs`); `all_preprocessed_column_ids`
emits **46** columns (4 round split-pack ×5 + 4 σ split-pack ×3 + 4 range + 10
selectors), not the stale "94" its module doc claims. The decode/majch/xor
`*_column_ids` getters and `SigmaDecodeEval`/`MajChEval`/`Xor8Eval` survive only
for the standalone tests.

Consequence: **the Maj/Ch table-width tuning the brief asks about is moot** — that
table is not in the mdoc proof. The redesign target is exactly the shared module:
**8 split-pack tables + 4 range tables**, all keyed by 16-bit limbs.

### 0.2 The shared module (`crates/stwo-sha256/src/shared_tables.rs`)

12 producers, keyed by 16-bit limbs (`LOG_SIZE_16 = 16`), each committed at the
**Class-D blinded** size `blind_log_size = log_size + 1` (`SharedProducer::blind_log_size`,
doubling factor = 2, confirmed). Each producer carries value columns + a
`is_dummy` selector (preprocessed) + one multiplicity column (base trace); chunks
of 1–2 same-size producers each yield one paired `SecureField` interaction column
(`SECURE_EXTENSION_DEGREE = 4` base cols, `finalize_logup_in_pairs`).

| producer group | tables | value cols (`producer_preprocessed_cols`) | real→blinded rows |
|---|---|---|---|
| RoundSplit (Σ0/Maj, Σ1/Ch × lo/hi) | 4 | key+4 grp + is_dummy = **6** | 2^16 → 2^17 |
| SigmaSplit (σ0, σ1 × lo/hi) | 4 | key+2 grp + is_dummy = **4** | 2^16 → 2^17 |
| Range16 (terminal 16-bit limb) | 1 | val + is_dummy = **2** | 2^16 → 2^17 |
| Range2 / Range4 / Range5 (add carries) | 3 | val + is_dummy = **2** | 2^4 → 2^5 |

Chunking (`PRODUCER_PAIRS`): 9 log-16 producers → 4 pairs + 1 single (Range16);
3 log-4 ranges → 1 pair + 1 single ⇒ **7 chunks**, 5 at 2^17, 2 at 2^5.

### 0.3 Reconciliation (exact — model validated)

```
preprocessed = 4·6·2^17 + 4·4·2^17 + 2·2^17 + 3·2·2^5
             = 3,145,728 + 2,097,152 + 262,144 + 192          = 5,505,216   ✓ (target 5,505,216)
base trace   = (4+4+1)·1·2^17 + 3·1·2^5 = 1,179,648 + 96       = 1,179,744   ✓ (target 1,179,744)
interaction  = 5·4·2^17 + 2·4·2^5       = 2,621,440 + 256      = 2,621,696   ✓ (target 2,621,696)
                                                    shared TOTAL = 9,306,656  (= "9.31 M")
```

All three sub-totals reproduce the measured numbers to the cell. The shared
tables are **83%** of the 11.25 M-cell mdoc proof; the 4 message components are
~1.31 M; the rest (~0.63 M) is non-SHA glue.

### 0.4 Per-round consumer cost (current, from `constraints.rs`)

`wire_round_split_pack` / `wire_sigma_input_split` each fire the lo- **and**
hi-half relation (2 lookups). Complementary-gated pairs (`gate_r0`/`gate_not_r0`)
count once.

* round family (all t): a-operand, Maj, e-operand, Ch → 4 ops × 2 halves = **8**/row
* schedule family (t ≥ 16): σ-input-split(W15), (W2) → 2 × 2 = **4**/row
* average split-pack: 8 + (48/64)·4 = **11 lookups/row**
* range (mod-2³² add carries Range2/4/5, schedule Range4, terminal Range16) ≈ **5/row**
* trace columns/row: 32-bit planes for W,a,b,c,e,f,g + σ/Maj/Ch/T1/T2 limbs +
  packed-group cols + carries (`ROUND_COLS`, `SCHEDULE_ENTRY_COLS = 62`, …) — the
  split-pack **group values are expressions over the bit-planes**, not extra
  committed columns.

---

## 1. Partition existence (per function, per width) — see partitions.txt

Derived programmatically from the FIPS rotation constants (script output committed
as `tasks/sha-limb-redesign-partitions.txt`). Two results:

1. **O0/O1/O2 classification** (Appendix-A reproduction): Σ0/Σ1/σ0 = 11/11/10,
   σ1 = 12/12/8, Maj/Ch bit-local. This is the soundness basis the split-pack
   tuple inherits; the redesign does not disturb it.
2. **Per-limb fragmentation.** A packed group `packed(G)=Σ bit_{pos_k}·2^k` is
   **linear** in the bits, so a group straddling a limb boundary recombines as
   `packed(G)=Σ_L packed(G∩L)·2^{offset_L}` — a **degree-1** identity, available
   unconditionally for every function and width. Fragment counts (drive columns):

   | width | #limbs/word | S+S′ fragments/word (all 4 functions) | max frag bits |
   |---|---|---|---|
   | 8 | 4 | 8 | 5–6 |
   | 12 | 3 | 6 | 7 |
   | 16 | 2 | 4 | 8–10 |

   Every limb carries exactly one S and one S′ fragment (2/limb, uniform). w=8's
   fragment budget (8/word) equals the current 16-bit scheme's (4 groups × 2
   halves), but each fragment now sits in a 2⁸-row table instead of 2¹⁶.

**Degree/engine check (all candidates):** recombination = deg 1; producer emits
one gated fraction per limb-table (`finalize_logup_in_pairs`, ≤ deg 2 after
lifting); PAIRS-ONLY batching preserved; `max_constraint_log_degree_bound =
log_size + 1` holds for every producer. Table values ≤ 2^w ⇒ free range check.
No constraint exceeds degree 2.

---

## 2. Cell / lookup arithmetic

Redesign model: split-pack table keyed by a w-bit limb, value cols = `key + 2
S/S′ fragments + is_dummy` (= 4), one mult trace col, Class-D blinded (+1). Range16
replaced by one `Range_w` table (+ the 3 unchanged small ranges). Producers paired
into interaction chunks by equal size.

| scheme | split-pack tables | preprocessed | base trace | interaction | **shared TOTAL** |
|---|---|---|---|---|---|
| **current (w=16)** | 8 | 5,505,216 | 1,179,744 | 2,621,696 | **9,306,656** |
| **w = 8** | 16 | 33,984 | 8,800 | 18,688 | **61,472** (−99.3%) |
| w = 12 (12+12+8) | 12 | 286,912 | 75,872 | 168,192 | 530,976 (−94.3%) |
| w = 16 (minimal 2-frag) | 8 | 4,456,640 | 1,179,744 | 2,621,696 | 8,258,080 (−11.3%) |

* **w=8 is the sweet spot.** Rows drop 2¹⁷→2⁹ (256×) while tables only double
  (8→16) — a net ~150× on preprocessed. w=12's 2¹³ limbs make it 8× heavier than
  w=8 for a smaller consumer saving; w=16-minimal shows the row count, not the
  fragment count, is the cost driver (dropping groups 4→2 barely moves it).
* Going below w=8 cannot save more table mass (already negligible) but keeps
  multiplying consumer lookups — pure loss. w=8 is the optimum.

### Consumer-side growth (w=8, per message, ×4)

Each 16-bit-half split-pack lookup → 2 byte lookups; range h_out Range16 → 2×
(t=63 only, amortized ~0). Byte keys and fragments are **linear expressions over
the already-committed 32 bit-planes**, so **base trace does not grow — only
interaction does.**

* split-pack lookups/row: 11 → **22**; total consumer lookups/row 17.5 → 28.5 (**×1.63**)
* message cells 1.31 M → ~1.72–1.89 M (+0.4–0.58 M, depending on interaction share)

### Net SHA subsystem (tables + 4 messages)

```
10,616,656  →  ~1,865,000     save ~8,751,000 cells  (−82%)
total mdoc proof 11,250,000 → ~2,499,000  (×0.22)
```

Even a pessimistic doubling of message interaction leaves an overwhelming net win:
the fixed 9.3 M table mass dwarfs the per-message growth (tables are 7× the entire
message budget).

---

## 3. Predicted prove numbers

Anchored on the TS13 baseline (961 ms warm-MT / 2584 ms 1-thread) and the given
stage profile (`tree0_commit` 31/215 ms, `tree2_write` 90 ms of which `sha_tables`
56 ms; commit + FFT + quotient + FRI scale ~linearly with total cells). Total cells
×0.22. `sha_tables` `tree2_write` 56 ms → ~0.4 ms.

| assumption (cell-scaling share of prove) | warm-MT | 1-thread |
|---|---|---|
| 65% scales with cells | **475 ms (−51%)** | **1277 ms (−51%)** |
| 50% scales with cells (conservative) | **587 ms (−39%)** | **1579 ms (−39%)** |

Both cases clear the 15% bar by 2.5–3.5×. Secondary effects (small): consumer
witness-gen does ~1.6× more split-pack multiplicity accumulation; preprocessed
cache rebuild is cheaper. Proof **size** also drops materially (fewer committed
columns in tree0/tree1/tree2 → smaller Merkle caps + FRI, though FRI depth is set
by the max-domain component, likely a message/ECDSA component, not the tables).

---

## 4. Risk register (soundness-sensitive spots)

| # | risk | assessment / mitigation |
|---|---|---|
| R1 | **Range-boundedness of new limbs.** Each byte fragment must be `< 2^w`. | Free by construction: the w-bit table enumerates all `[0,2^w)` keys; membership *is* the range check (invariant I-3). Verify the fragment cols are consumed (use, +mult), never yielded, on the consumer side. |
| R2 | **Multiplicity aliasing across the 2× tables.** More tables/producers → more `PRODUCER_PAIRS` chunks, more `*_column_ids`, more relations. | Mechanical layout risk (I-5 / layout-consistency), not a new soundness class. Every table keeps its own namespaced ID + relation; the existing `column_ids_follow_documented_order` + fingerprint-guard patterns extend directly. Add a partition-regression test mirroring `round_groups_subdivided_for_w6`. |
| R3 | **Dummy-key collisions (Class-D).** Blinded upper half `[2^w, 2^{w+1})` must stay disjoint from real keys and gate the numerator by `(1−is_dummy)`. | Unchanged mechanism; `blind_extend` + `emit_blind` are width-agnostic. At w=8 the reserved region is `[256,512)` — verify `is_dummy` selector regenerated per new table. |
| R4 | **Recombination linearity.** `packed(G)=Σ packed(G∩L)·2^{offset}` must be exactly the offsets in partitions.txt. | Degree-1, but offset arithmetic is a silent-drift hazard. Derive offsets programmatically from the S-masks (not hand-typed) and pin with a test that reassembles the full word from fragments == identity. |
| R5 | **Blinding domain vs SIMD floor.** w=8 → 2⁹ blinded, 2⁸ real; well above `LOG_N_LANES=4`. No under-pad risk. | OK. (w=4 would hit the floor — another reason to stop at 8.) |
| R6 | **σ1 asymmetry (12/12/8).** σ1's O2=8 differs from the 10 of the others. | Handled identically — fragmentation is per-bit, independent of the O0/O1/O2 counts. partitions.txt confirms 2 frags/limb for σ1 too. |

No new soundness *class* is introduced: the redesign is a re-keying of existing
single-input membership tables, and single-input tables shrink cleanly (no
2-operand `2^{2w}` blow-up — the eliminated xor_8 was the only pair-keyed table
and it is already gone from this path).

---

## 5. Recommendation

**Go / no-go bar:** reject if predicted total prove-time win < 15%.
**Result: ACCEPT — build w = 8.** Predicted win 39–51%, ~3× the bar; 99.3% table-mass
reduction; no degree/engine/soundness obstruction; consumer growth (base trace flat,
interaction ×1.63) is dwarfed by the fixed table saving.

**Rejected alternatives:** w=12 (8× heavier tables than w=8, uneven limbs, extra
Range_12); w=16 / status quo (row count unchanged — the real cost driver); w<8
(no further table saving, more consumer lookups).

### Do this first (rung 1 — likely dominates w=8)

The census exposes a bigger prize than the brief scoped. On this branch the
consumer **already commits full 32-bit boolean planes** and boolean-constrains
them, and the split-pack "groups" are linear expressions over those planes. The
split-pack lookup's remaining job is to bind a **limb-carried working-state value**
(`a_new@−1`, `h_in[·]`, `maj`, `ch`) to that bit form and range-check it. That
binding can plausibly be a **direct degree-1 recomposition constraint**
(`a_prev_lo == Σ_{i<16} a_bits[i]·2^i`, etc.) with **no table and no lookup at
all** — removing the 9.3 M table mass *and* the split-pack consumer lookups
(shrinking the messages too), a strictly larger win than w=8.

Before building w=8, spend ~½ day confirming what the split-pack lookup enforces
that a recomposition constraint would not (working-state ↔ bit-plane consistency
across rows; any range check on carried limbs not otherwise covered). Decision
tree:

* **If the lookup is redundant** → delete the split-pack tables entirely (rung-1
  YAGNI); skip w=8. Biggest win, smallest diff.
* **If it is load-bearing** → implement w=8 as specified here (§1–§2). Still a
  decisive, well-scoped win.

Either branch clears the bar comfortably; killing the table via rung 1 is the
lazier and larger outcome, so it is checked first.

---

## Split-pack replaceability verification (adversarial)

Verified against `feat/sha-limb-redesign` @ `716aab9a`. Read-only; all claims
cited to `crates/stwo-sha256/src/`. **Verdict: REPLACEABLE — stronger,
DELETABLE with zero compensating constraints.** The §5 rung-1 hypothesis holds,
and holds harder than §5 hedged: the packed-group machinery is already
vestigial on this branch, so no new recomposition constraint is even needed —
the constraints that make deletion sound (booleanity + limb recomposition)
already exist in the AIR for an independent reason.

### The one structural fact that decides it

On this branch every SHA round/schedule function is computed **directly from
committed 32-bit boolean bit-planes**, not from the packed groups:

* `sigma0_bits = big_sigma0_expr_bits(a_bits)`, `sigma1_bits = big_sigma1_expr_bits(e_bits)`,
  `maj_bits = maj_expr_bits(a_bits,b_bits,c_bits)`, `ch_bits = ch_expr_bits(e_bits,f_bits,g_bits)`
  — `constraints.rs:504-507`; the `*_expr_bits` bodies are pure
  index-permutation + XOR over the bits (`constraints.rs:1149-1207`).
* those output bits are recomposed into the output limbs `sigma0/sigma1/maj/ch`
  (`constraints.rs:508-511`), and the four mod-2³² adds of the round consume
  **only limbs** (`emit_mod_2_32_add_linear`, `constraints.rs:591-636`).
* the schedule σ is identical: `sched_sigma{0,1}_bits` are constrained equal to
  `lower_sigma{0,1}_expr_bits(w_m15/w_m2 bits)` (`constraints.rs:372-375`) then
  recomposed into `s0/s1` (`376-377`). `w[15]`/`w[2]` never reach the σ result
  through the packed cells.

The packed-group cells (`a_grp,e_grp,maj_grp,ch_grp`, `b_init,c_init,f_init,g_init`)
and the σ-input split cells (`sched_sigma0_split,sched_sigma1_split`) are consumed
**exclusively** by the split-pack lookups. Grep evidence: `a_grp`→531/541,
`e_grp`→561/571, `maj_grp`→515(tie)/551, `ch_grp`→516(tie)/581,
`sched_sigma*_split`→382/390 only; `b_init/f_init` are read `[0,-1]` but the `-1`
element (`_init[i][1]`) is referenced nowhere — only `_init[i][0]` feeds the t=0
lookup (`constraints.rs:311-314,327-357`). Nothing in the arithmetic touches them.

Consequence: the split-pack lookup's *only* residual soundness role is the
implicit **range check** it advertises ("implicitly range-checks the limb to
[0,2¹⁶)", `constraints.rs:1039-1040,1093`). Every other purported role (packing,
cross-representation binding) is dead weight.

### Q1 — what each of the 8 lookups enforces today

Tuple shapes: RoundSplit `(key, g0..g3)` = `ROUND_SPLIT_PACK_REL_SIZE`
(`wire_round_split_pack`, `constraints.rs:1042-1085`); SigmaSplit
`(key, packed_s, packed_s_complement)` = `SIGMA_SPLIT_PACK_REL_SIZE`
(`wire_sigma_input_split`, `constraints.rs:1094-1121`). Key = the 16-bit limb
half (`word.0`/`word.1`); outputs = packed-group / packed-`s` cells.

| lookup (relation) | key limb, gate | output cells | (a) linear packing? | (b) key range from table only? | (c) cross-rep binding? |
|---|---|---|---|---|---|
| sigma0_lo/hi | `a_prev`=`a_new@-1` (`gate_not_r0`) / `h_in_0` (`gate_r0`) / `maj` (`enabler`) | `a_grp` / `maj_grp` | yes — `pack_round_group_exprs(a_bits)` (`245`), `maj_grp` tied to `pack(maj_bits)` (`515`) | **no** — key recomposed (see Q's below) | only for `maj_grp`, already duplicated by `515` |
| sigma1_lo/hi | `e_prev`=`e_new@-1` / `h_in_4` / `ch` | `e_grp` / `ch_grp` | yes — `247`, `ch_grp` tied by `516` | **no** | only for `ch_grp`, duplicated by `516` |
| sigma0_lo/hi (t=0 aux) | `h_in_1`,`h_in_2` (`gate_r0`) | `b_init_now`,`c_init` | packing **not** otherwise constrained | **no** | **yes — this lookup is `b/c_init`'s only tie to bits today** |
| sigma1_lo/hi (t=0 aux) | `h_in_5`,`h_in_6` (`gate_r0`) | `f_init_now`,`g_init` | packing not otherwise constrained | **no** | **yes — only tie for `f/g_init`** |
| lower_sigma0_lo/hi | `w[15]` (`gate_sched`) | `sched_sigma0_split` | packing not otherwise constrained | **no** | none — σ0 result already from bits |
| lower_sigma1_lo/hi | `w[2]` (`gate_sched`) | `sched_sigma1_split` | packing not otherwise constrained | **no** | none — σ1 result already from bits |

So of the four possible roles: (a) packing is either already an expression or a
redundant tie; (b) **no key is range-bounded by table membership alone** — see
Q1b; (c) the only genuine cross-rep binding is for `b/c/f/g_init`, and it binds
committed group cells that feed nothing but the lookup itself; (d) no
dummy/padding role beyond the standard `enabler`-gated multiplicity
(`constraints.rs:1056-1062`).

### Q1b — is any keyed limb bounded ONLY by table membership? No.

`limb_sum` sums exactly `LIMB_BITS=16` boolean bits per limb
(`constraints.rs:1209-1214`; `LIMB_BITS=16` `types.rs:14`, `WORD_BIT_COLS=32`
`trace.rs:107`). `constrain_boolean_bits` is **ungated — every row**
(`constraints.rs:1236-1240`, called `470-478`). So any limb constrained
`limb == Σ_{i<16} bit_i·2^i` with boolean bits is forced into `[0,2¹⁶)`; that is
the *same* free range check R1 credits to the table. Every split-pack key has
such a recomposition:

* `a_prev`/`h_in_0` ← `a_in` recomposed to `a_bits`, `constraints.rs:481`
  (gated `enabler` ⊇ both `gate_not_r0` and `gate_r0` on real rows;
  `a_in`=`h_in_0` at t=0, `=a_new@-1` at t≥1 via `boundary_select`).
* `e_prev`/`h_in_4` ← `e_in`→`e_bits`, `constraints.rs:482`.
* `h_in_1/2/5/6` ← `b/c/f/g_bits`, `constraints.rs:483-486` (gated `gate_r0`).
* `maj`,`ch` ← recomposed ungated, `constraints.rs:510-511`.
* `w[15]`,`w[2]` are cross-row reads of the single W-limb column, which is
  recomposed on its home row via `w[0]`→`w_bits`, `constraints.rs:480` (gated
  `enabler`; home rows t−15, t−2 are real in-block rows). There is no separate
  `w[15]` column to forge — `w[k]` are offset reads of one column
  (`constraints.rs:157-169`).

No keyed limb lives only as a limb; none depends on the table for its range.

### Q2 — booleanity on padding / message-schedule rows

`constrain_boolean_bits` is ungated, so `w,a,b,c,e,f,g,sched_sigma0/1` bit
columns are boolean on **every** row including padding and the message region
(`constraints.rs:470-478`). Recomposition and the lookups are all `enabler`- (or
finer-) gated, so padding rows (`enabler=0`) contribute nothing and cannot inject
junk. The malicious-junk-in-inactive-rows attack is blocked by ungated
booleanity, not by the lookup — deleting the lookup does not open it.

### Q3 — the 4 range tables survive independently

`Range2/4/5` bound the mod-2³² add carries (`emit_mod_2_32_add_linear` →
`wire_range_check`, `constraints.rs:591-636,1366-1397`); `Range16` bounds the
final-block **digest** limbs `h_out[j]` (`constraints.rs:683-696`), which have
**no bit-plane** and so genuinely need it. None of these consume split-pack
membership, and deleting split-pack shifts no burden onto them: the split-pack
keys are bounded by recomposition, not by any range table. (The
`shared_tables.rs:~696` "keys ≥ 2¹⁶ unreachable" note concerns the Range16
producer's own domain and is orthogonal.) The four range producers stay exactly
as they are.

### Q4 — external consumers

No consumer of the `SplitPack*` relations or the group/`packed_s` columns exists
outside `stwo-sha256` (grep of `crates/eu-id-prover/src`, `crates/stwo-p256/src`
for `SplitPack|split_pack|_grp|packed_s` → empty). The mdoc field-exposure path
takes SHA state through **recomposed, boolean-constrained bits**, explicitly
"so no [lookup needed]" (`field_exposure.rs:13`); exposed digest bytes are
bounded by Range16, not split-pack. No γ-digest / window-bind relation
transitively depends on split-pack for boundedness or well-formedness.

### Q5 — VERDICT (a) REPLACEABLE / DELETABLE

Delete the 8 split-pack producers, their 8 `SplitPack*` relations, and all
consumer call sites (`wire_round_split_pack`, `wire_sigma_input_split`).
**Compensating constraints needed: none** — booleanity (`470-478`) and limb
recomposition (`480-486`,`510-511`) already cover every key's range, and the
arithmetic never reads the groups. Additionally delete the now-dead committed
columns and their generators: `maj_grp`,`ch_grp` (16 cols) and the two ties
`constraints.rs:515-516`; `b_init,c_init,f_init,g_init` (32 cols);
`sched_sigma0_split,sched_sigma1_split` (8 cols) — ≈ **56 base cols/row removed**
across the 4 message components. `a_grp`/`e_grp` are expressions, not columns, so
they vanish with the call sites. No bit column becomes free: `a,b,c,e,f,g,w`
bits still feed Σ/σ/Maj/Ch and the reuse chain (`constraints.rs:492-502`).

* **Degree:** deletion only removes constraints/relations; all survivors are the
  existing ≤ deg-2 identities. No engine/PAIRS-ONLY concern.
* **Cell delta vs the doc's w=8:** strictly better on every axis. w=8 keeps the
  group machinery, re-keys the tables to 61k cells but **grows** message
  interaction ×1.63 (+0.4–0.58 M). Deletion removes the ~8.4 M of split-pack
  producer mass outright (leaving only the ~0.6–0.9 M of retained range
  producers, Range16-dominated) **and shrinks** the messages (−56 cols/row,
  interaction drops rather than grows). Net SHA subsystem lands at or below
  w=8's ~1.865 M as a pure-deletion diff with no new tables to audit. If `h_out`
  is later given a bit-plane + recomposition, Range16 too could go and the shared
  table mass approaches zero — a follow-on, out of scope here.
* **Invariants to pin as negatives before/after the diff:** (i) mutate a keyed
  limb off its bit-recomposition (e.g. add 2¹⁶ to `maj`) ⇒ recomposition
  (`510`) must reject — proves the range check truly lives in recomposition, not
  the deleted lookup; (ii) write non-boolean junk into an inactive-row bit ⇒
  ungated booleanity (`1238`) must reject; (iii) round-trip proof unchanged after
  deletion (completeness).

### Q6 — the doc's ×1.63 consumer census is correct; no consumer missed

Enumerated consumers of split-pack: round family fires 4 ops × 2 halves = 8/row
(`constraints.rs:527-586`, complementary `gate_r0`/`gate_not_r0` pairs count
once), schedule family 2 × 2 = 4/row (`378-393`), plus 4 t=0-only aux sites × 2
halves (`323-362`). Average `8 + (48/64)·4 = 11`/row, matching §0.4; w=8's
11→22 doubling is arithmetically right. But it is moot: deletion removes these
consumers rather than doubling them, so the ×1.63 interaction growth never
occurs.
