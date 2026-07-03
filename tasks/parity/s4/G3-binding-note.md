# G3 — Cross-field binding argument (architect note, 2026-07-03)

**Status:** ARCHITECT-WRITTEN, done. Unblocks BL5; the implementation spec is
`../mailbox/answers/Q-017.md`. Candidates considered were G0 §5's A (Longfellow
two-field MAC) and B (shared-point MLE openings of small limbs). **v1 selects
neither: the binding surface is public in v1, so the sound and minimal argument is
shared-transcript statement binding.** The MAC (candidate A) is specified below as
the v2 upgrade for when the statement values go private.

## 1. What actually needs binding
After BL6 deletes stwo-p256, the M31 STARK proves SHA-256 + digest-bind + predicates;
the F_p256 coprocessor proves the ECDSA circuit (WO-G4). The only values living on
both sides are the ECDSA statement scalars: `z` (per signature), `r, s, Qx, Qy`, and
the blind indices `i₁, i₂` (Q-022). In v1 **all of these are public**: `r, s, Q` are
public today (recorded privacy caveat), and `z` already appears verbatim in the
serialized `PublicEcdsaInstance` limbs of the current monolith — treating it as a
public input changes nothing observable. What must NOT be merely public is the
*meaning* of `z`: `z = SHA-256(C)` stays proven in-circuit on the M31 side.

## 2. The v1 binding argument (normative)
1. **One Blake2s channel.** The M31 STARK and the coprocessor share a single
   Fiat-Shamir channel (scope §2). All coprocessor challenges are drawn from channel
   state that has already absorbed (a) the M31 side's commitments in their existing
   order, (b) the domain-separation tag `b"eu-id-ec-coproc-sumcheck-v1"` + circuit
   shape, (c) the **full public ECDSA statement** — `z, r, s, Qx, Qy` per signature
   plus blind indices and blind points `B, D` — as 32-byte BE field elements, and
   (d) the BL3 Ligero commitment root. Statement bytes are absorbed **before** the
   Ligero root, which is absorbed before any sumcheck or opening challenge.
2. **Coprocessor side:** C1/C2 (WO-G4) bind the witnessed limbs to those public felt
   values in-circuit. The verifier computes the expected statement itself and rejects
   on any mismatch with what was absorbed — prover-supplied bytes never enter.
3. **M31 side:** the digest-bind bridge re-targets from the (deleted) P256 module's
   z-limbs to the **public** `z`: it becomes a public-digest-bind (the exact
   construction already shipped in `eu_id_prover::mdoc::PublicDigestBind`) requiring
   the public 32 bytes of `z` on the SHA `Sha256Digest` LogUp relation. Global LogUp
   balance then enforces `z = SHA-256(C)` against the *same* public value the
   coprocessor bound its limbs to.
4. **Soundness:** both proof systems are sound w.r.t. their public inputs; the public
   inputs are byte-identical because the verifier constructs them once and absorbs
   them once into the shared channel before any challenge on either side. There is no
   cross-field claim to argue beyond Fiat-Shamir domain separation (distinct tags for
   the M31 segment and the coprocessor segment; no absorb-order ambiguity because the
   order is normative and any deviation changes every subsequent challenge).
   Soundness error added by binding: 0 beyond the two systems' own errors.

## 3. Rejection conditions (verifier-side, all REQUIRED, each with a negative test)
1. Statement mismatch: expected `(z,r,s,Q,i,B,D)` ≠ proof's absorbed statement.
2. LogUp imbalance: `z ≠ SHA-256(C)` (public-digest-bind breaks the global balance).
3. Coprocessor rejection: any BL2 round check, the closing relation, any BL3
   Merkle/proximity/consistency check.
4. Transcript-order violation: any reordering of absorbs (detected by challenge
   divergence — test by swapping two absorbs in a doctored prover).
5. Config/parameter mismatch: BL3 parameters not the pinned Q-020 set; M31 PCS
   config not the pinned profile.

## 4. v2 — when z / r / s go private (unlinkability phase): the Longfellow MAC
Recorded now so nobody re-derives it; do NOT build in v1. Port of paper §3.4
(Protocol 3.1 / Theorem 3.2) as actually shipped (verified against both
implementations 2026-07-03):
- MAC is `mac_i = (a_p,i + a_v) · x_i` over GF(2^128) (no `+b` term — deviation from
  the paper, acknowledged in the code; requires MACed values ≠ 0 and adds a small ZK
  error; soundness 2^-128 per 128-bit half).
- Each 256-bit common value splits into two GF(2^128) halves; per half the prover
  commits a key share `a_p,i` inside each field's witness commitment; the single
  verifier share `a_v` is squeezed from the shared channel **after both commitments
  are absorbed**; the tags `m_i` become public inputs to BOTH circuits; each circuit
  re-verifies its MAC in-circuit (the F_p256 side simulates GF(2^128) on bit vectors;
  a new gadget on our M31 side — the real cost of v2).
- References: paper §3.4; C++ `lib/circuits/mac/mac_circuit.h`,
  `lib/circuits/mdoc/mdoc_zk.cc` (`generate_mac_key`, `update_macs`); Rust
  `src/mdoc_zk/prover.rs`, `src/mdoc_zk/layout.rs`.
