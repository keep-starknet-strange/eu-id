# WO-BL3 — Mini-Ligero commitment + ZK sumcheck (OTP transcript)

**Depends:** WO-BL1 (`Fp`, `Mle`, Blake2s channel), WO-BL2 (`InputClaims` handoff), G0 §3 params, WO-G5. **Blocked until G1/G2/G4 pass, G3 acked.** Lives in `crates/eu-id-ec-coprocessor/`, module `ligero.rs` + `zk.rs`.

Normative references: Longfellow eprint 2024/2010 §2.2 (Ligero, Thm 4 = AHIV23 Thm 5.4) and §2.3 (ZK protocol, OTP construction); AHIV17/AHIV23 for the base Ligero analysis. The ZK/OTP part MUST NOT be improvised (G0 §3, scope §6b).

---

## §1 Commitment — matrix layout (`ligero.rs`)
Per G0 §3: witness ≈ 1,100 `Fp` values/sig + OTP pad columns (~2× ⇒ budget ~2,300 values). Longfellow §2.2 splits input into public `x` + private witness `w`.
1. **Pack** the witness `Vec<Fp>` (BL2's input-layer values `V_d` ‖ the ZK pad values from §4) into an `m × k` matrix, row-major, `Fp::ZERO`-padded. **Starting params (G0 §3): rate 1/4, k = 64, N = 256, t = 180.** `m = ⌈total_values / k⌉`. Record actual `m` for the sig circuit.
2. **RS-encode each row** `k → N` (rate `k/N = 1/4`). **Naive Lagrange encoding (spell out, G0 §3 "naive Lagrange fine at this size"):** treat the `k` row values as evaluations at fixed domain points `x_0..x_{k-1}` (use `Fp::from_u64(0..k)`); interpolate the degree-`<k` polynomial; evaluate at `N` fixed points `x_0..x_{N-1}` (superset) ⇒ codeword row. Reuse BL1 `Mle`/Lagrange helpers or add `rs_encode(&[Fp], eval_points: &[Fp]) -> Vec<Fp>` to a small `rs.rs`. No NTT (p256 has no smooth subgroup — scope §0; paper §2.2 confirms P256 lacks efficient NTT).
3. **Merkle over COLUMNS:** each of the `N` columns is `m` `Fp` values (32 B each) ⇒ hash to a leaf with **Blake2s (reuse the existing hasher, do not add a dep)** — `TODO(verify): locate the Blake2s Merkle helper already in the tree (grep found blake2s use under crates/predicates/ and air-core channel); reuse its leaf/node hashing, or the raw blake2s crate if no reusable Merkle exists.` Commitment `com` = Merkle root, mixed into the BL2 channel BEFORE any sumcheck challenge (scope §2 step 3, BL2 §4 line 1).

## §2 Opening protocol — the exact checks (`ligero.rs`)
Verifier draws `t = 180` random column indices from the channel. For the opened columns the prover reveals the full column (`m` values) + Merkle path. Two checks (AHIV23 / paper §2.2):
1. **Merkle-path check:** each opened column hashes to a leaf consistent with `com`. Reject on mismatch.
2. **Proximity test (row is a codeword):** verifier draws a random vector `γ ∈ F^m`, prover sends the claimed combined codeword `u = Σ_i γ_i · (row_i encoded)` (a length-`N` vector, i.e. the encoding of `Σ γ_i row_i`); verifier checks, at each opened column index `c`, that `u[c] == Σ_i γ_i · Column_c[i]`. This ties the committed columns to a low-degree (codeword) row space. `u` must itself be a valid RS codeword (degree `< k`) — verifier re-encodes `u`'s first `k` entries and checks the rest, OR checks `u` lies in the code by the standard interleaved-Ligero test.
3. **Consistency test (linear/quadratic constraints):** the sumcheck-verifier's checks are re-expressed as linear (and `d` quadratic) constraints on the committed values (§4). Prover sends the claimed linear-combination row(s); verifier checks the combination at each of the `t` opened columns equals `Σ_i (constraint-coeff)_i · Column_c[i]`. This is the paper's "Ligero constraints on the committed pad values."

## §3 Soundness-parameter computation — IMPLEMENTER FILLS, ARCHITECT ACKS (REQUIRED, do not skip)
Cite the **exact source: Longfellow §2.2, the Appendix-C-improved AHIV23 bound.** The paper states overall soundness error is bounded by:
```
  (1 − e/n)^t  +  ((k+ℓ)/n)^t  +  (2k/n)^t  +  (n+3)/|F|
```
with AHIV23 Thm 4 constraints: `e < (n−k)/2`, `n > 2k+e`, `k > ℓ+t`, `|F| ≥ ℓ+n`, `m·ℓ > n_i + s` (`n=N=256` codeword length, `k=64`, `ℓ` = ZK masking degree, `t=180`, `s` = circuit size, `n_i` = input length).
**The implementer MUST:** (1) plug our `n=256, k=64, t=180, |F|=p≈2^256` and a chosen `ℓ, e` into all four terms; (2) show the sum `≤ 2^-128`; (3) if it does not, RAISE `t` (or `N`) per the formula — **parameters are adjusted by this computation, not by feel** (G0 §3). (4) Note that `(n+3)/|F| ≈ 2^-248` is negligible; the binding rows are `(1−e/n)^t` and `(2k/n)^t = (1/2)^{180}` — verify `(2k/n)^t = 2^-180` clears the budget, and pick `e` so `(1−e/n)^t ≤ 2^-128`. **Write the filled computation into this file's §3-RESULT block and get architect ack (Q-003/Q-004 review pattern) BEFORE BL3 code merges.**
`TODO(architect): ack the filled §3-RESULT — the choice of ℓ and e and the ≤2^-128 arithmetic. This gate mirrors G3's role for binding.`

## §4 ZK — Longfellow's OTP-masked-transcript construction (§2.3, restate step-by-step; NO improvisation)
Plain sumcheck leaks the witness (G0 §3). Longfellow's fix: commit `(witness ‖ one-time pads)`, run sumcheck on **masked** messages, and let Ligero prove the decrypt relation as `d` quadratic + `d+1` linear constraints. The paper (§2.3, Protocol 2.5) is abstract; **the normative algebra is draft-google-cfrg-libzk-01 §6.5–6.6 and the reference implementations** — full extraction with public coefficients in `../mailbox/answers/Q-018.md` (architect-verified 2026-07-03 against the C++ and the ISRG Rust port; the two interoperate on shared test vectors). Steps:
1. **Commit pads first**, in the §1 Ligero matrix under `com`: per half-round a **pair** `[dP(0), dP(2)]` (only `p(0)` and `p(2)` are ever sent; `p(1) = claim − p(0)` is implied — Q-018/BL2 amendment), and per layer a **claim-pad triple** `[dW_L, dW_R, dW_LR]` with `dW_LR = dW_L·dW_R` computed at pad-sampling time and committed like any other value.
2. **Prover sends masked messages:** `p̂(t) = p(t) − dP(t)` for `t ∈ {0,2}`, and per layer `vl̂ = w(L) − dW_L`, `vr̂ = w(R) − dW_R` (sign convention `value − pad`, matching draft/code and their test vectors).
3. **Round recursion as symbolic linear terms** (draft §6.6): maintain `sym_claim` affine in committed pads; per half-round `sym_p1 = sym_claim − sym_p0`, then `sym_claim ← lag₀(c)·sym_p0 + lag₁(c)·sym_p1 + lag₂(c)·sym_p2` — this subsumes the `p(0)+p(1)=c` check; no separate constraint.
4. **Closing constraints per layer** (`Q` = the verifier-computed bound-quad scalar, our "q(L,R)"):
   linear — `symbolic − (Q·vr̂)·dW_L − (Q·vl̂)·dW_R − Q·dW_LR = Q·vl̂·vr̂ − known`;
   quadratic — `dW_L · dW_R = dW_LR`. Exactly one of each per layer.
   ⚠ draft-01 prints the RHS as `Q·vl̂·vl̂` — a **typo**; both implementations compute `Q·vl̂·vr̂` (code is authoritative).
5. **Global input binding (once):** draw `γ`; `Σᵢ eq2[i+npub]·w_priv[i] − dW_L^{last} − γ·dW_R^{last} = −Σᵢ eq2[i]·x_pub[i] + claim₀ + γ·claim₁` with `eq2 = bind(EQ,G₀) + γ·bind(EQ,G₁)`.
6. **Ligero proves** these `d+1` linear + `d` quadratic constraints against `com` via §2's opening (t columns); each quadratic constraint `(x,y,z)` costs 3 extra tableau rows (draft §4.4.2).
Line-by-line implementation reference: Rust port `src/sumcheck/mod.rs::run_protocol` + `src/sumcheck/constraints/mod.rs`; C++ `lib/zk/zk_common.h` (`ConstraintBuilder`, `PadLayout`, `setup_lqc`).

## §5 Test plan (`cargo test -p eu-id-ec-coprocessor`)
- **RS round-trip:** encode `k` random values → decode first `k` codeword positions ⇒ identity; corrupt one codeword symbol ⇒ proximity test rejects.
- **Commit/open KAT:** commit a known matrix, open `t` columns, verify Merkle + proximity + consistency accept; corrupt one column value ⇒ reject; wrong `com` root ⇒ reject.
- **End-to-end ZK sumcheck:** wire §4 onto a small BL2 circuit, prove→verify accepts; then per adversarial class (tamper a padded message, a pad column, a Lagrange coeff, the final quadratic constraint) ⇒ reject.
- **Input-layer opening (BL2 §5 tie-back):** `InputClaims.values[i] == Ṽ_committed(points[i])` proven via the opening; mutate a value ⇒ reject.
- **Leakage smoke test (REQUIRED, informal):** two DIFFERENT witnesses `w_a, w_b` satisfying the SAME public statement → produce their full transcripts (encrypted messages + opened symbols) under many fresh channel seeds; collect the byte distributions and run a **chi-square sanity check** that the two transcript-symbol distributions are statistically indistinguishable (not a formal ZK proof — a regression guard against an obvious OTP mistake, e.g. a reused or zero pad). Assert the chi-square statistic stays below a loose threshold; a failure means a pad leaked.

## §6 Acceptance
`cargo test -p eu-id-ec-coprocessor` green including the leakage smoke test; §3-RESULT filled and architect-acked; proof-size recorded honestly in perf-log.md (G0 §3 estimate ~230 KB pre-optimization — record the real number, packing tricks out of scope v1).

## Out of scope
Subfield/packing proof-size optimization (G0 §3 — v2), cross-field binding (BL5), the ECDSA circuit (BL4), stwo modification, eu-id-prover wiring, a formal ZK proof (smoke test only).

## §7 G5 FORK
If WO-G5 verdict = VENDOR and the port ships a usable Ligero+OTP core: adapt per BL2 §8's checklist (license header, BL1 `Fp` + Blake2s channel bridge, keep §5 tests including the leakage smoke test, keep §3 soundness computation regardless of code origin). The §3 architect-ack and §4-step-6 `TODO(architect)` gate apply to vendored code too — vendoring does not waive the parameter proof.
