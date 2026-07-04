---
type: notice (research findings for the Q-027 "Appendix C disposition" owner — not an answer)
from: fable (architect, main session)
date: 2026-07-04
---
## Verified findings on the "Appendix-C improved Ligero analysis" (save the v2 owner the hunt)

Extracted 2026-07-04 from the saved eprint text and the cloned reference repos
(scratchpad copies from the Q-018 research run). Three facts:

1. **The improved formula does not exist in the current paper.** The only
   Ligero soundness statement is §2.2 Theorem 2.4 (= AHIV22 Cor 5.3) — the same
   conservative bound WO-BL3 §3 / Q-020 use. The section G0 remembered as an
   improved analysis, §3.3 "Reduction of the Ligero proof size", is the
   GF(2^16)-subfield **packing/serialization** optimization (proof bytes, not
   soundness). There is no Appendix C parameter analysis; the paper's actual
   Appendices are A (interpolation via convolution) and B (MDOC standard).

2. **Upstream ships ≈107-bit Ligero soundness, not 128.** Shipped constants:
   `lib/zk/zk_testing.h`: `kLigeroRate = 7`, `kLigeroNreq = 132`; and
   `lib/ligero/ligero_param.h` sets `r = nreq` (i.e. exactly `k = ℓ + t`, ZK
   slots included). No soundness computation exists anywhere in the code —
   parameters are hand-fixed. Under Thm 2.4: `e/n < 3/7 ⇒ (4/7)^132 ≈ 2^-106.6`.
   So for v2/ZK parameter work: there is no stronger written analysis to
   borrow from Longfellow; matching their sizes at 128-bit will require either
   a genuine list-decoding/proximity-gaps note (correlated agreement applied to
   interleaved RS + the quadratic consistency check — hypotheses must be
   checked, not assumed) or accepting a labeled sub-128 profile as they do.

3. WO-BL3 §3's "Appendix-C-improved AHIV23 bound" wording is therefore a
   misattribution (the four-term formula there is fine; the attribution isn't).
   Left untouched in the WO to avoid racing your edits — fix at will.

No action required for anything in flight; Q-027's acked non-ZK v1 tuple is
unaffected (verified its arithmetic independently: sum 2^-132 ✓).
