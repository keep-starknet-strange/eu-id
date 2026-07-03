# WO-BL4 — ECDSA verify circuit + hint generation in `eu-id-ec-coprocessor`

**Status:** build WO (S4-lite Phase-2, #10). **Spec = WO-G4-circuit-inventory.md** (its rows are normative).
**Depends:** BL1 (`Fp`, `Mle`, `batch_inverse`), BL2 (layered-circuit struct + sumcheck). **Blocked by** G4 ack.
**Out of scope:** cross-field binding (BL5), eu-id-prover integration + stwo-p256 deletion (BL6).
**Oracle for hints:** the `p256` v0.13 crate (`ProjectivePoint`, `AffinePoint`, `Scalar`, `NonZeroScalar`).

## 1. Circuit-builder API (`circuit.rs`)
Populate BL2's layered-circuit struct. **One builder fn per G4 family**, named for the family, each appending
gates + declaring the witnesses it binds. Signature convention: `fn cN_<name>(b: &mut CircuitBuilder, w: &WitnessRefs) -> ()`.
- `c1_input_limbs`, `c2_input_canonicality`
- `c3_sinv`, `c4_u1`, `c5_u2` — each takes the mod-n `(a,b,c,q)` refs, emits the `a·b = q·n + c` limb identity + `<n` gates.
- `c6_scalar_bits` — booleanity βⱼ²=βⱼ and Σβⱼ2^j = uₖ.
- `c9_ladder_u1g`, `c10_ladder_u2q` — loop 256 steps calling shared `double_step` / `cond_add_step` helpers.
- `c11_final_add`, `c12_on_curve` (called for every point ref registered by C9/C10/C11), `c13_slope_inverses`.
- `c14_final_check`, `c15_infinity_guards`.
- `build_ecdsa_verify(b) -> Circuit` — calls the above **in inventory order**; that order defines layer assignment.
Reuse `Fp` mul/square/add from BL1; do not reimplement field ops. Mod-n constant `n` = P256_ORDER as `Fp` limbs.

## 2. Hint generation (`hints.rs`) — prover-side witness computation
`fn generate_witness(input: &EcdsaVerifyInput) -> Result<Witness, HintError>`. Uses the `p256` crate as the
oracle for all reference arithmetic; the circuit re-proves it. Exact oracle calls:
- Parse z,r,s → `Scalar` (`Scalar::from_repr`, big-endian). Reject non-canonical (C2 surface).
- `sinv = s.invert()` (`NonZeroScalar::invert`, constant-time not required — prover-local).
- `u1 = z * sinv`, `u2 = r * sinv` (`Scalar` mul, already mod n). Quotients q_inv,q₁,q₂ computed as
  `(a*b - c) / n` on the **integer** (BigUint) products, stored as `Fp` limbs.
- Ladders: recompute each accumulator via **explicit affine double-and-add** (do NOT call the crate's
  fused `lincomb` — we need every intermediate point). Base points: G (from `types::generator`), Q (input).
  Slope denominators collected and `batch_inverse`d (BL1) in one pass; store both the point and its slope-inv.
- `R = u1*G + u2*Q` affine; `r' = R.x mod n`, reduction flag `k = (R.x >= n) as u8`.
- **Determinism:** no RNG, no threads, no `HashMap` iteration in witness layout — same input ⇒ byte-identical
  witness vector. Assert this in tests (§4). Ladder = **MSB-first over all 256 bits from a blinded start**
  `acc_0 = B = (i+1)·G`, public blind index `i` starting at 0 (canonical spec: `../mailbox/answers/Q-022.md`;
  the earlier "LSB-first" wording here was an error). Blind index is part of the deterministic output.
- **Edge handling (G4 policy = reject-and-regenerate):** if any intermediate = 𝒪 or any slope denom = 0,
  return `HintError::ExceptionalTrace` — the caller bumps the blind index `i → i+1` and re-derives (Q-022 §3).
  For real p256 signatures at `i = 0` this never fires; the error path is exercised by a synthetic edge test (§4c).

## 3. Witness-layout contract with BL3 (STABLE ordering)
BL3 (commitment) reads the witness as a flat `Vec<Fp>`. Order is **frozen** here; any change is a mailbox event.
| slot range | contents | count |
|---|---|---|
| 0..100 | input limbs (z,r,s,Qx,Qy × 20) | 100 |
| 100..101 | sinv | 1 |
| 101..103 | u1, u2 | 2 |
| 103..106 | q_inv, q₁, q₂ | 3 |
| 106..618 | u1_bits (256), u2_bits (256) | 512 |
| 618..1130 | u1G acc pts `acc_1..acc_256` (× x,y) | 512 |
| 1130..1642 | u2Q acc pts `acc_1..acc_256` (× x,y) | 512 |
| 1642..1646 | S₁, S₂ corrected endpoints (x,y each) | 4 |
| 1646..2159 | u1G denom-inverses (`[λD,λA]` × 256 + correction) | 513 |
| 2159..2672 | u2Q denom-inverses (idem) | 513 |
| 2672..2673 | C11 final-add denom-inverse | 1 |
| 2673..2675 | R.x, R.y | 2 |
| 2675..2677 | reduction flag k, r' | 2 |
| 2677..2680 | infinity flags | 3 |
| **len** | | **2680** |

(LAYOUT v2 per `../mailbox/answers/Q-022.md`; supersedes the original 2159-slot table.
Public-input `x` region additionally carries blind indices i₁,i₂ and B₁,D₁,B₂,D₂ coords.)
Expose as `const LAYOUT: &[(&str, Range<usize>)]` so BL3 and tests share the single source of truth.

## 4. Test plan
**(a) KATs — round-trip real signatures.** Generate ≥ 20 signatures with the `p256` crate
(`SigningKey::sign` over random messages), build `EcdsaVerifyInput`, run `generate_witness` → assert the
circuit is satisfied (BL2 evaluator returns all-zero constraint poly). Include the NIST P-256 test vector.
Assert byte-identical witness on repeat (determinism).

**(b) Per-family negative tests — one mutation per G4 row that MUST make the circuit reject.** (soundness campaign seed)
| target | mutation | expected |
|---|---|---|
| C1 | flip one input limb (recompose ≠ felt) | reject |
| C2 | set r = 0 / r = n | reject |
| C3 | corrupt sinv (s·sinv ≠ 1 mod n) | reject |
| C4 | corrupt u1 (≠ z·sinv) | reject |
| C5 | corrupt u2 | reject |
| C6 | set a u1 bit to 2 (non-boolean) | reject |
| C8/C12 | move a table/accum point off-curve (x+=1) | reject |
| C9 | corrupt one u1G accumulator step output | reject |
| C10 | corrupt one u2Q accumulator step output | reject |
| C11 | corrupt R = u1G⊕u2Q output | reject |
| C13 | replace a slope-inverse with a wrong value | reject |
| C14 | set r' = R.x when R.x ≥ n but leave k=0 (skip wrap) | reject |
| C14 | valid R but claim r ≠ R.x mod n | reject |
| C15 | force an infinity flag = 1 | reject (unsatisfiable, per policy) |
Each mutation targets exactly one family; a mutation that only trips a *different* family than intended is a
spec bug — file mailbox. This table is the negative-test manifest BL6's campaign extends.

**(c) Two edge-case policies tested.**
1. **u1 ≡ 0 (mod n)** synthetic input ⇒ u1G = 𝒪 ⇒ `generate_witness` returns `ExceptionalTrace`, then the
   blinded regeneration path produces a satisfying witness. Assert both: error fires, retry succeeds.
2. **P = −P vertical slope** in a ladder step (crafted accumulator) ⇒ slope denom = 0 ⇒ same reject-then-
   regenerate. Assert the pinned infinity flag (C15) cannot be set to smuggle it (mutation from table 4b/C15).

## 5. Acceptance
- All KATs pass; every negative-test row rejects; both edge policies behave as specced.
- `LAYOUT` len = 2159, matches G4 witness ledger; gate count from `build_ecdsa_verify` printed and ≤ 35k.
- No `Fp` op reimplemented (reuse BL1); no witness outside `LAYOUT`; determinism assertion green.
