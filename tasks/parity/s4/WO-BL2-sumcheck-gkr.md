# WO-BL2 — Sumcheck/GKR prover + verifier over F_p256 (production)

**Depends:** WO-G2 (constant confirmed), WO-G5 (VENDOR vs WRITE verdict), WO-BL1 (`Fp`, `Mle`, channel). **Blocked until G1/G2/G4 pass, G3 acked** (README Phase 2).

Lives in `crates/eu-id-ec-coprocessor/`, module `sumcheck.rs` + `circuit.rs`. Field-generic over BL1's `Fp` (NOT stwo). Longfellow eprint 2024/2010 Protocol 2.2 ("VerifyP,V(C,x)") is the normative reference; stwo `sumcheck.rs`/`gkr_prover.rs` are structural references only.

---

## §1 Data model (`circuit.rs`)
Longfellow §2.1 layered-quad model — implement exactly:
- **Layers 0..d**, layer 0 = output, layer d = input. Layer `j` has width `w_j`, `ω_j = ⌈log2(w_j)⌉`.
- **One gate type: the quad.** `V_j[i] = Σ_{ℓ,r ∈ {0,1}^{ω_{j+1}}} Q_j[i,ℓ,r]·V_{j+1}[ℓ]·V_{j+1}[r]`. Add and mul and const are all encoded as quad terms (paper §2.1: `V_j[0]=1` by convention makes add/const uniform — enforce `V_j[0]==Fp::ONE` for every layer). No separate gate enum: `enum GateKind { Add, Mul, Const }` MAY exist as a *builder* convenience but MUST lower to quad terms.
- **Wiring:** `Q_j` as a sparse list `Vec<QuadTerm { out: u32, l: u32, r: u32, coeff: Fp }>` per layer (real circuit is sparse — do not densify). Provide `Q_tilde_eval(&self, layer, &[Fp] r_out, &[Fp] L, &[Fp] R) -> Fp` = Σ over terms of `coeff · eq(out,r_out)·eq(l,L)·eq(r,R)` where `eq` is the multilinear equality MLE (BL1 `Mle` supplies `eq`; if not, add `eq(&[Fp],&[Fp])->Fp` to `mle.rs`).
- **Witness assignment:** `Vec<Vec<Fp>>` = the `V_j` arrays, width-`w_j` (power-of-two padded with `Fp::ZERO`, BL1 `Mle::new` convention). `satisfied()` = all `V_0[i] == 0` (paper: input satisfies iff all layer-0 outputs are 0).

## §2 Prover (`sumcheck.rs`, per-layer, Protocol 2.2 step 2)
State entering layer `j`: two points `(r_{j,0}, r_{j,1}) ∈ F^{ω_j}` and two claims `(c_{j,0}, c_{j,1})` asserting `c_{j,b} = Ṽ_j(r_{j,b})`. Bootstrap (step 1): verifier draws `r ∈ F^{ω_0}`, sets `r_{0,b}=r`, `c_{0,b}=0`.
1. **Fold two claims into one (step 2a):** draw `α_j ← channel`; set `Y = α_j·c_{j,0} + (1−α_j)·c_{j,1}`. **This RLC of the two point-claims is the G0 §2 soundness-budget mechanism** — one sumcheck instead of two, error additive `≤ 3·(2ω_{j+1})/p` per layer.
2. **Build `g_j` (step 2b):** the `2·ω_{j+1}`-variate poly
   `g_j(L,R) = [α_j·Q̃_j(r_{j,0},L,R) + (1−α_j)·Q̃_j(r_{j,1},L,R)] · Ṽ_{j+1}(L) · Ṽ_{j+1}(R)`.
3. **Sumcheck the claim `Y = Σ_{L,R} g_j(L,R)` (step 2c):** run the round loop of WO-G2 §2 over `v = 2ω_{j+1}` variables. Round poly degree ≤ **2** per variable (the wiring MLE and exactly one of Ṽ(L)/Ṽ(R) are degree 1 in each variable — Q-018 amendment; the earlier "degree 3 / evaluate at {0,1,2,3}" was wrong). Evaluate at `{0,1,2}`; **transmit only `p(0)` and `p(2)`** — `p(1) = claim − p(0)` is implied and never sent (Longfellow draft §6.4–6.5 and its test vectors). Mix, draw `ρ`, fold. Produces points `(ℓ, r)`, value `y`, claim `y = g_j(ℓ,r)`.
4. **Emit next claims (step 2d):** `c_{j+1,0} = Ṽ_{j+1}(ℓ)`, `c_{j+1,1} = Ṽ_{j+1}(r)`. Set `(r_{j+1,0}, r_{j+1,1}) = (ℓ, r)`. Recurse to layer `j+1`.
5. **Final layer (step 3):** `c_{d,b}` are claims about `Ṽ_d` = the **input layer** = the committed witness ⇒ handed to BL3 (see §5).

**RLC across many gate-groups / instances:** if a layer carries multiple independent sub-claims (e.g. batching several sigs), combine with a single `λ`-power RLC before the sumcheck (imitate stwo `random_linear_combination(&polys, lambda)` in `sumcheck.rs`, and `generate_secure_powers`-style `λ^i` weighting) — one `λ` draw, powers `λ^0,λ^1,…`. Soundness cost additive per G0 §2.

## §3 Verifier (`sumcheck.rs`)
Per layer, per round: reconstruct `p(1) = c − p(0)` from the received `p(0), p(2)` (the sum check is thereby structural, not an equality test), draw `ρ` from the **same** channel, set `c = p(ρ)` via `⟨λ_ρ, (p(0),p(1),p(2))⟩` Lagrange interpolation (paper §2.3 "dot-product ⟨λr,(p(0),p(1),p(2))⟩"). After the loop, step 2e check:
`y == [α_j·Q̃_j(r_{j,0},ℓ,r) + (1−α_j)·Q̃_j(r_{j,1},ℓ,r)] · c_{j+1,0} · c_{j+1,1}`.
Final (step 3): the input-layer claims `c_{d,b} == Ṽ_d(r_{d,b})` are NOT evaluated locally — they are **handed to BL3's commitment opening** (§5). The verifier accepts iff every per-round + step-2e check passes AND BL3 confirms the two input-layer openings.

## §4 Transcript rules (NORMATIVE — deviation is a mailbox question, README non-negotiable)
Mix into the shared Blake2s channel (BL1 `channel.rs`), in this exact order, per layer `j = 0..d`:
1. (once, before layer 0) domain-separation tag `b"eu-id-ec-coproc-sumcheck-v1"` + circuit shape (`d`, all `w_j`) + **the public ECDSA statement** (per signature: `z, r, s, Qx, Qy`, blind index `i`, blind points `B.x, B.y, D.x, D.y` — G3 note / answers/Q-017.md item 3) + the BL3 witness-commitment root, in that order (statement precedes commitment precedes challenges).
2. draw `α_j`.
3. for each sumcheck round `k`: mix `p_k(0), p_k(2)` (32-byte BE each, in that index order; `p(1)` implied — Q-018 amendment) → draw `ρ_k`.
4. mix `c_{j+1,0}, c_{j+1,1}` (the emitted next-layer claims) BEFORE moving to layer `j+1`.
Every `Fp` mixed as 32-byte BE via BL1's `mix` entrypoint. Two-field tag collision: resolved by G3 §2 — the coprocessor segment absorbs its own domain tag into the shared channel state after the M31 segment; order is normative (answers/Q-017.md item 3).

## §5 Input-layer handoff to BL3 (no unbound claims — README non-negotiable)
The two final claims `c_{d,b} = Ṽ_d(r_{d,b})` are evaluations of the committed witness MLE at points `r_{d,b}`. BL2 exports `struct InputClaims { points: [Vec<Fp>;2], values: [Fp;2] }`; BL3 proves each `values[i] == Ṽ_committed(points[i])` via its MLE-eval opening (scope §2 step 6, the S1-B1 tie-back lesson). BL2 does NOT trust these values — they are only accepted after BL3's opening verifies.

## §6 Test plan (`cargo test -p eu-id-ec-coprocessor`)
- **KAT vs brute force:** build small circuits (d=2..4, w ≤ 2^6), evaluate `V_j` directly (dense loop), assert `Ṽ_d(r) == prover's c_{d,b}` and full prove→verify accepts. Include a real ECDSA-shaped micro-circuit once BL4 lands (feature-gated).
- **Adversarial — every mutation class MUST reject:** (a) flip one `Q_j` coeff; (b) flip one witness `V_j[i]`; (c) tamper one round poly `p_k(t)`; (d) skip the `α_j` fold (use `c_{j,0}` only); (e) wrong final `c_{d,b}` value with correct point; (f) reorder two transcript mixes (§4 order violation). Each in its own `#[test]`, asserting `Err`/reject.
- **Determinism:** same witness+channel-seed ⇒ byte-identical transcript.

## §7 Acceptance
`cargo test -p eu-id-ec-coprocessor` green; prover wall-time on the G4 circuit within 20% of the G2 projection (record in perf-log.md per README); workspace builds; `ec-coprocessor` feature not yet wired into eu-id-prover (BL6).

## Out of scope
Ligero/ZK/OTP (BL3), cross-field binding (BL5), ECDSA circuit definition (BL4 — G4 inventory is its spec), stwo modification, eu-id-prover wiring, verifier succinctness (paper notes it is omitted; we do not need it).

---

## §8 G5 FORK — if WO-G5 verdict = VENDOR, replace §1–§3 with this checklist
Keep §4 (transcript), §5 (handoff), §6 (tests), §7 (acceptance) UNCHANGED — they are our soundness surface regardless of code origin.
1. **License:** copy the ISRG port's license header verbatim into every vendored file; add the source URL + commit hash + license line to `crates/eu-id-ec-coprocessor/VENDORED.md`. If license ∉ {MPL, Apache-2.0, MIT} ⇒ STOP, mailbox (WO-G5 gate already required this, re-confirm).
2. **API surface to adapt:** (a) field type → make its sumcheck generic over, or newtype-bridge to, BL1 `Fp`; (b) transcript/Fiat-Shamir → replace its hasher with BL1's Blake2s channel, preserving §4 mix order (this is the highest-risk adaptation — their absorb order may differ; audit against §4 line-by-line); (c) circuit builder → adapt to our `QuadTerm` layout or wrap theirs; (d) input-layer claim export → expose `InputClaims` (§5) from their final-round output.
3. **Conformance tests to KEEP (do not delete when vendoring):** all of §6, plus a **cross-check test**: run one statement through both the vendored path and (if G2's prototype survives) the reference prototype, assert identical accept/reject. Add their upstream test vectors as an additional `#[test]` if they ship any (WO-G5 rubric row "test vectors").
4. **Strip:** any of their code we do not use (their ECDSA circuit if BL4 owns ours; their PCS if it is not the BL3 Ligero we spec) — KEEP ONLY ACTIVE CODE (house rule). Record what was stripped in VENDORED.md.
5. If any adapted module fails §6 adversarial tests ⇒ treat as WRITE for that module (fall back to §1–§3), mailbox the divergence.
