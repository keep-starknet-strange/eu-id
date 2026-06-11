# γ-digest reshape: one provide per row instead of one fraction per range use

Status: APPROVED design (user: "if it's sound then go"), worksheet written before
implementation per the AIR-writer discipline. Companion of the wide mul-result
tuple rework and the hinted-mul provider.

## 0. Problem

After the hinted-mul fold campaign the monolith still spends most of its
interaction width on **per-value range-check fractions emitted by wide
consumer rows**. Measured (1 signature, post-pkc-fold, total 8,816 M31
interaction columns):

| component | rows | M31 interaction cols | logup entries/row | of which range13+signed uses |
|---|---|---|---|---|
| fake_glv_projective_source | 2^8 | 1,976 | 986 | 940 |
| prepared_table_projective_source | 2^4 | 2,100 | 986 | 940 |
| scalar_setup | 2^4 | 1,296 | ~324 | majority |
| final_add.check | 2^4 | 1,260 | 315 | 300 |
| public_key_on_curve.curve_check | 2^4 | 612 | 153 | 140 |

A use fraction costs 4 M31 interaction columns (1 QM31 logup column,
batch-2 halves it) **per wide row**, even though the verifier only needs
*multiset membership of the value in a range table*. 95% of the two worst
components is exactly this.

## 1. Property spec (what must remain true)

For every wide row `r` and every value `v` in its fixed use-column list
`U = [c_0, .., c_{L-1}]` (a compile-time constant per component):

> `base[r][c_i] ∈ T_kind` for the designated table `T_kind`
> (range13 = [0, 2^13), or the signed-carry table, or range9),

with the same binding strength as the current per-value LogUp use against the
component's range relation. Nothing else about the wide component's
constraints or other relations changes.

## 2. Algorithm (redesign heuristic H2: probabilistic verification)

Replace the L per-value fractions of row `r` by **one digest provide**:

- Draw `γ ∈ QM31` from the channel **after the base trace commit** (the
  digested values are committed before γ exists).
- Wide side commits, per row and per kind, a 4-column QM31 interaction-tree
  value `D_r` constrained (degree 1, ungated) by
  `D_r = Σ_{i<L} base[r][c_i] · γ^i`,
  and yields ONE tuple on a new `GammaDigest` relation:
  `(tag, row_index, D_r.0, D_r.1, D_r.2, D_r.3)` with multiplicity
  `−present_r` (`present_r` = preprocessed activity flag, §5.3).
- A **tall expander component** (one instance per (component, kind)) carries
  the same values as a base value grid of K columns per row
  (`K = GAMMA_DIGEST_LANES`), a running QM31 accumulator
  `acc_row = acc_prev · γ^K + Σ_{j<K} v_j · γ^{K−1−j}`
  (reset at preprocessed group starts), uses the digest tuple
  `(tag, row_index, acc)` with multiplicity `+end_flag` at each preprocessed
  group end, and emits **K range fractions per tall row** against the SAME
  range relation instance the wide component used before.

The range providers' multiplicity columns are unchanged (same multiset of
consumed values, now consumed from the tall rows).

Net: L fractions/row → 1 digest fraction/row on the wide side; the tall side
pays K fractions + 4 acc columns per ceil(L/K)-row group at a much smaller
column count (§7).

## 3. Layout manifest

### Wide side (per adopted component, per kind present)
- interaction tree: +4 M31 columns (the QM31 digest D), +1 logup fraction
  (the digest yield) folded into the existing batched finalize.
- base tree: unchanged.
- preprocessed: `present` flag column (often reuses the existing row-index /
  active schedule column; see §5.3).
- constraints: +1 EF constraint (4 M31 constraints) `D − Σ v_i γ^i = 0`,
  ungated, degree 1.

### Tall expander instance (per (component, kind))
```
log_size           = padded_log_size(ceil(L/K) · scheduled_wide_rows)
base columns       : v_0 .. v_{K-1}                       (K columns)
preprocessed       : tag      (constant per instance, can be folded into relation)
                     row_id   (wide row_index this tall row belongs to)
                     start    (1 on first row of each group)
                     end      (1 on last row of each group)
interaction        : acc (4 M31 = 1 QM31, custom EF column, mask [-1, 0])
                     logup: K range-use fractions + 1 digest-use fraction,
                            batch-2 → ceil((K+1)/2) QM31 columns
constraints:
  C1  acc − (1−start)·acc_prev·γ^K − Σ_j v_j·γ^{K−1−j} = 0      degree 2
  C2  (logup batched finalize)                                   degree ≤ 3 at log+1 (batch 2 ⊕ numerator deg ≤ 1)
row ordering: Pattern B for acc (offset −1), groups laid out contiguously
  in coset order: group g occupies rows [g·ceil(L/K), (g+1)·ceil(L/K)).
padding rows: all-zero values, start=end=0 ⇒ acc keeps multiplying by γ^K
  (acc of padding = acc_last·γ^K·…, unconsumed, unconstrained boundary — fine,
  no fraction is emitted because end=0 and range fractions get numerator
  `present_tall` = preprocessed in-group flag).
```
Initial `K = 8` (tune after measurement). With L=940: 118 tall rows per wide
row.

## 4. Relation contracts

### `GammaDigestRelation` (new), arity 6: `(tag, row_index, d0, d1, d2, d3)`
| field | meaning |
|---|---|
| tag | static id of (component, kind) — disjoint across all instances |
| row_index | wide row's preprocessed index (matches tall group's preprocessed row_id) |
| d0..d3 | QM31 digest limbs |

| site | sign | multiplicity | tuple |
|---|---|---|---|
| wide row (adopted component) | yield (−) | `present_r` (preprocessed) | (tag, row_index, D_r) |
| tall group end | use (+) | `end` (preprocessed) | (tag, row_id, acc) |

One relation instance drawn once in the monolith, shared by all adopted
components; tags keep tuples disjoint. Balance: per (tag, row_index), yield
and use cancel iff `D_r == acc(group)` as QM31 values.

### Range relations (existing, per component silo)
Use side moves from the wide row (L entries, numerator gated as today) to the
tall rows (K entries/row, numerator = preprocessed in-group flag, i.e. each
scheduled value is consumed exactly once, unconditionally). Provider
multiplicity columns: regenerated from the same values — tallies unchanged
except formerly *gate-suppressed* values (inactive formula blocks) are now
counted; those values are constrained zero / valid encodings on honest traces
(§5.4) so the provider multiplicity gen simply tallies the tall grid.

### Public data
None of the digest machinery touches public inputs; I-4 unaffected.

## 5. Soundness argument

### 5.1 Binding chain
```
wide base values v_i  --(degree-1 constraint, γ post-commit)-->  D_r
D_r  --(GammaDigest LogUp, tags+row_index)-->  acc(group)
acc(group)  --(C1 recurrence over preprocessed group layout)-->  tall values v'_j
tall values  --(range LogUp, unchanged relation)-->  range table membership
```
A malicious prover who wants an out-of-range wide value must either
(a) break a LogUp balance (soundness of the existing argument, ~2^-124),
(b) find `acc(group) == D_r` with a different value sequence: both sides are
evaluations at γ of degree-(L−1) polynomials with coefficients fixed at
base-commit time (wide: trace columns; tall: value-grid columns, committed in
the SAME base tree before γ is drawn). Distinct polynomials agree at γ with
probability ≤ (L−1)/|QM31| ≈ 940/2^124 < 2^-114 — Schwartz–Zippel, γ
channel-drawn after the commitment that fixes both coefficient vectors, or
(c) tamper with tags/row_index/group layout: all preprocessed (pinned by the
preprocessed-root check at verify time), and tags are globally disjoint
constants, so no replay of one row's digest into another row/component/kind.

### 5.2 The four invariants
- **I-1 witness uniqueness**: D is uniquely determined by the base values
  (ungated degree-1 identity). acc is uniquely determined by start flags +
  value grid (C1 is ungated; at start rows the acc_prev term is multiplied
  by (1−start)=0, so the recurrence pins acc on EVERY row including group
  starts). Tall value grid itself is the witness being proven — bound by the
  digest equality to the wide values.
- **I-2 logup balance**: digest yield/use signs follow the stwo convention
  (provider −, consumer +); per-tag-and-row pairing is enforced by the tuple
  fields. The slice/monolith balance accounting adds one
  `GammaDigest` entry: Σ wide yields + Σ tall uses = 0.
- **I-3 domain enforcement**: every digested value gets exactly one range
  use on the tall side, numerator preprocessed-1 (stronger than the previous
  witness-gated numerators: no prover-controlled gate can skip a check).
- **I-4 public binding**: untouched.

### 5.3 The preprocessed schedule (presence) requirement
The digest yield multiplicity and the tall group layout are PREPROCESSED, so
the set of digest-carrying rows must be witness-independent. This holds for
the adopted components: the ladder schedule, prepared-table rows, final_add /
curve-check / scalar_setup active rows are deterministic per signature count
(the existing preprocessed row-index/schedule columns encode exactly this).
Witness-dependent gates (e.g. `has_muls`, formula-kind flags) do NOT gate the
digest: all use-list columns are digested unconditionally (§5.4). If a future
component has genuinely witness-dependent activity, it cannot adopt the
gadget without a witness-dependent-multiplicity redesign — documented here as
a hard precondition.

### 5.4 Unconditional digestion of conditionally-used values
Previously some use fractions had witness gates (inactive formula block ⇒ no
fraction). The digest includes those columns unconditionally; the tall side
range-checks them unconditionally. Honest traces hold zeros (or valid
encodings) in inactive blocks — zero ∈ range13, zero-carry encoding ∈ signed
table, so completeness holds; soundness only gains (formerly uncheckable
garbage in inactive blocks is now range-bound). Provider multiplicities are
regenerated from the unconditioned grid. Adoption checklist item per
component: verify inactive-block padding is in-table on honest traces (it is
for all five candidates: blocks are zero-initialized).

### 5.5 Degree worksheet
| site | expression | degree | bound |
|---|---|---|---|
| wide digest def | `D − Σ v_i γ^i` (γ^i constants) | 1 | log+1 ✓ |
| wide digest yield | numerator `present` (preprocessed) | 1; batched ⊕ ≤ 3 | log+1 ✓ |
| tall C1 | `acc − (1−start)·acc_prev·γ^K − Σ v_j γ^{K−1−j}` | 2 | log+1 ✓ |
| tall logup | numerators preprocessed flags, batch 2 | ≤ 3 | log+1 ✓ |

All within the empirically-validated ceiling (degree ≤ 3 at `log_size + 1`,
batch ≤ 2 — see the degree-bound rule memory/commit).

## 6. Adversarial test plan
| invariant | malicious change | expected failure |
|---|---|---|
| value binding | flip one digested wide base limb after build (provider stays) | GammaDigest imbalance (digest ≠ acc) |
| tall grid lie | flip one tall value-grid cell (digest matches wide) | GammaDigest imbalance OR range imbalance |
| out-of-range smuggle | put 2^13 in a wide use column + matching tall cell | range13 imbalance (provider lacks the value) |
| replay | swap two rows' digests (same tag) | row_index mismatch → imbalance |
| acc reset lie | zero a start flag in a forged preprocessed tree | preprocessed root mismatch at verify |
| gate-skip (old hole) | nonzero garbage in an inactive formula block | now range-checked: imbalance (previously unchecked!) |

Plus the standing monolithic battery (e2e prove+verify, mutated-hint tests)
must stay green.

## 7. Cost model & phased adoption
Per adopted wide component: ~L/2 QM31 logup columns removed per row-width,
+1 fraction +4 M31 columns. Tall instance ≈ K + 4 + 4·ceil((K+1)/2) + 3
M31 columns at log_size ≈ log2(rows·L/K).

Phases (measure shape + proof size + e2e after each):
- **A**: gadget components + adopt `fake_glv_projective_source`
  (1,976 → ~110 wide cols + tall ~36 cols at ~2^15) — the largest single win.
- **B**: adopt `prepared_table_projective_source` (2,100 → ~110 + tall at 2^11).
- **C**: adopt `final_add.check`, `public_key_on_curve.curve_check`,
  `scalar_setup` (range9 kind added), `final_check`.
- **D** (optional): consolidate per-component range relations/providers.

Projected total after C: 8,816 → ~2.5–3k M31 interaction columns,
proof ≈ 2.5–3 MB.
