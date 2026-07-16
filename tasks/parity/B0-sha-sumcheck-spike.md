# B0 — Boolean-sumcheck SHA kill-switch spike (Path B decision gate)

Machine: Apple M2 Max, 12 cores, NEON. rustc 1.94.0-nightly. Single-thread.
Standalone crate: `scratchpad/sha-sumcheck-spike` (NOT a workspace member; own
empty `[workspace]`). Release + `target-cpu=native`, fat-LTO, 1 codegen-unit.
best-of-3 wall time (1 warm-up discarded). Binary: `./target/release/spike`.

## Pre-registered decision rule (written BEFORE any measurement)

**Timestamp ordering (explicit):** this section was authored at
**2026-07-06T21:03Z**, before the crate compiled or produced a single number
(the first successful run was ~21:10Z). The rule was fixed first; the numbers
did not get to move the line.

Verbatim from WO-B0:

> projected mdoc SHA side = ns/term × terms/block × block-count(fixture)
> + input-commit estimate.
> - **GO** (fund Path B design): projection ≤ 350 ms single-thread M-class
>   (≥3× vs the 1,082 ms STARK side, with engine-risk margin).
> - **NO-GO:** Path A is the ceiling.

Decision is Lucas's either way — this spike only produces the number.

## Circuit shape

One SHA-256 compression block as a **layered quadratic boolean circuit**, one
bit per wire, all modular 32-bit additions expanded to explicit ripple-carry
bit gates (no opaque arithmetic — the whole compression is a boolean DAG of
binary quadratic gates). Gates leveled by longest-path depth from inputs
(standard GKR layering).

| metric | value |
|---|---:|
| total gates | 127,738 |
| inputs (8 IV + 16 msg words + 2 consts, bit-expanded) | 770 |
| AND gates | 47,440 |
| XOR gates | 77,480 |
| NOT gates | 2,048 |
| layers (incl. input layer 0) | 3,920 |
| provable layers | 3,919 |
| **terms/block** (Σ pad2(layer_len) over provable layers) | **178,638** |

Layer pad2-size histogram (auditable divisor for ns/term):

```
pad2 -> #layers
    16 -> 696
    32 -> 1740
    64 -> 1271
   128 -> 206
  1024 -> 2
  2048 -> 1
  (2,4,8 -> 1 each)
raw gates in provable layers: 126,968
```

**Shape caveats (load-bearing for interpretation):**
- Gate count (127K) exceeds the WO's 30–60K target because ripple-carry adders
  are fully bit-expanded. A production Path B would use word-level / 2-bit add
  gadgets, cutting terms/block substantially. So **terms/block here is an
  over-count** relative to an optimized circuit.
- The circuit is **deep and thin**: 3,919 layers averaging ~32 gates. Every
  layer fits in L1, so the measured ns/term is a **thin-layer best case** with
  no memory-bandwidth cost. Parity-S3 measured the memory-bound regime
  (n_vars 16–22 wide layers) at **31.6 ns/term** for the same degree-2 gate
  class. A real design packing many blocks into wide layers would land nearer
  S3's constant. These two artifacts partly cancel (thin layers under-estimate
  ns/term; bit-adders over-estimate terms).

## Two encodings

(a) **M31 bit-per-wire.** {0,1}⊂M31; AND=a·b, XOR=a+b−2ab (here XOR realized as
    a native quadratic gate), NOT=1−a. This is the primary measured encoding.

(b) **GF(2^128) packed-XOR (Longfellow-style).** Field mul is hardware PMULL
    (`vmull_p64`) + GHASH reduction, **verified against the bit-serial
    reference copied from `crates/eu-id-ec-coprocessor/src/mac.rs::gf128_mul`**
    (10,000-pair KAT passes). NOTE: the circuit fed to GF128 here is still
    bit-per-wire (same 178,638 terms), which **throws away the entire point of
    the packed encoding** — in a true Longfellow circuit 32 bits pack into one
    element and the 77,480 XOR gates (60% of the circuit) become free additions,
    collapsing the term count ~. The GF128 number below is therefore a
    *pessimistic upper bound* on the packed cost; it cannot flip M31's verdict.

## Measured ns/term (best-of-3, single-thread)

Correctness gates that ran green before every timing (a wrong prover measures
garbage):
- circuit output bits == native SHA-256 compression (real KAT)
- M31 sumcheck claimed sum == independent direct Σ eq(r,x)·V(x)
- GF128 sumcheck claimed sum == independent direct Σ eq(r,x)·V(x)
- SIMD-M31 claim == scalar-M31 claim
- hardware PMULL gf128 == bit-serial mac.rs reference (10k KAT)

| encoding | runs (ms) | best (ms) | ns/term |
|---|---|---:|---:|
| M31 scalar | 1.877 / 1.966 / 1.972 | 1.877 | **10.51** |
| M31 SIMD (4× u64 NEON) | 1.368 / 1.370 / 1.490 | 1.368 | **7.66** |
| GF128 scalar (PMULL) | 4.508 / 4.612 / 4.875 | 4.508 | **25.23** |
| GF128 bit-serial (mac.rs as-is) | ~1448 (earlier build) | — | ~8100 |

The bit-serial gf128 from mac.rs is 840× slower than PMULL — do not cost Path B
on it; it is a correctness reference only.

## Projection arithmetic vs the 350 ms GO line

projection = ns/term × 178,638 terms/block × block-count + input-commit.

**Block-count (fixture):** the mdoc fixture proves **4 SHA instances** (issuer
Sig_structure, device Sig_structure, birth_date item, nationality item;
`crates/eu-id-prover/src/mdoc.rs:433–501`), each a COSE `Sig_structure`/item
preimage. ES256 Sig_structures run ~100–300 B ⇒ 2–5 SHA blocks each ⇒ **≈ 8–20
real blocks** for the fixture. I could not extract the exact count without
building the full workspace (shared dirty tree; >15 min). Per the WO fallback I
also report the **64-block stated assumption** (a deliberate over-estimate — it
corresponds to a padded-trace block-equivalent, not the real preimages).

| ns/term | 16 blk | 64 blk (assumption) | 128 blk |
|---|---:|---:|---:|
| M31 SIMD 7.66 | 21.9 ms | 87.6 ms | 175.2 ms |
| M31 scalar 10.51 | 30.1 ms | 120.2 ms | 240.5 ms |
| GF128 PMULL 25.23 | 72.1 ms | 288.4 ms | 576.9 ms |
| **stress: S3 wide-layer 31.6** | 90.3 ms | 361.3 ms | 722.6 ms |

**Input-commit estimate (labeled — NOT measured):** Path B still Ligero-commits
the input-layer wires so the sumcheck's input claims tie back. Basis: the
coprocessor probe's `merkle_ms = 77 ms` + `rs_encode 172 ms` for its current
witness. The SHA input layer is ~770 wires/block × block-count ≈ 12–50 K field
elements — the same order as, or smaller than, one existing coprocessor Ligero
column. Estimate **+80–180 ms** for the input commitment (row-commit + encode),
scaling sub-linearly with block-count. Add this flat to the SHA-side numbers
above.

Worked GO-line check at the two bracketing block-counts, M31 SIMD + commit:
- real fixture (≈16 blk): 21.9 + ~120 (commit) ≈ **142 ms** ✓ under 350
- 64-blk assumption: 87.6 + ~150 (commit) ≈ **238 ms** ✓ under 350
- stress (S3 constant, 64 blk): 361 + commit ≈ **510 ms** ✗ over 350

## GO/NO-GO indication

**Indication: GO (decision is Lucas's).**

The sumcheck-prover constant for the SHA gate class is **7.66–10.51 ns/term**
measured (M31, single-thread NEON), giving a SHA-side projection of **~90–240 ms
+ ~80–180 ms input-commit** at the realistic fixture block-count and even at the
conservative 64-block assumption — comfortably inside the 350 ms GO line, and
3–10× under the 1,082 ms STARK side of record.

**The verdict is NOT unconditional.** It flips to marginal-NO-GO only if BOTH:
(1) the real block-count is ~64+ AND (2) the production circuit lands in S3's
memory-bound 31.6 ns/term wide-layer regime rather than this L1-resident
thin-layer regime. That combination (361 ms + commit) exceeds the line. The two
biggest levers a Path B design must actually hit to bank the GO:
- **cut terms/block** below the 178,638 bit-expanded count via word-level add
  gadgets (the 77K XOR + adder bits are the fat);
- **keep the per-term constant in the ~8–11 ns regime**, i.e. avoid the
  memory-bound wide-layer penalty S3 saw, OR absorb it in the block-count.
GF128-packed (encoding b, properly implemented) is the natural way to erase the
XOR fat — its PMULL constant (25 ns/term) is higher per-term but over ~32× fewer
terms, a large net win the bit-per-wire spike could not capture.

Bottom line for the fund/close call: the measured constant clears the bar at the
fixture's real block-count with margin; fund Path B **design**, with the two
levers above written into its acceptance gates so the engine-risk margin is
defended by construction rather than by this spike's best case.
