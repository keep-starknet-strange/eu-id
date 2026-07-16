# Remaining work — precise work orders (architect, 2026-07-06)

Scope: EVERYTHING left on the mdoc/P4/TS13/hardening/parity tracks as of
`feat/proof-reductions @ 9e1ac686`. Each WO is self-contained: an implementing
agent executes it without reading the mailbox history. Facts below were
re-verified against the tree on 2026-07-06; line numbers drift — re-grep the
named symbol if a line doesn't match, do NOT guess.

## House rules (apply to every WO)

- `rtk` prefix on all commands. No pushes. No Co-Authored-By lines.
- Every perf claim = a named measured number in the report ("no number, not done").
  All single-thread numbers under `RAYON_NUM_THREADS=1`.
- NEVER weaken or `#[ignore]` a test to get green. On any STOP condition:
  write `tasks/mdoc-mailbox/questions/Q-0XX-<slug>.md` (next free number,
  currently Q-026+) with the failing output verbatim, then end with a report.
- Worktree agents: `git log -1 --format=%H` FIRST and verify the stated base
  commit before doing anything (worktrees have silently based on `main` before).
- New/changed proof bytes ⇒ re-pin fixtures is expected ONLY where a WO says so;
  anywhere else a byte change is a STOP.

## Dependency order

```
WO-0 (Q-021 gate evidence)          — first, main tree, verification only
WO-1 (merge predicate-binding)      — after WO-0
WO-2 (merge froot-pinning)          — after WO-1
WO-3 (A-004 offset re-binding)      — after WO-1 (same files), promotion gate
WO-4 (P4b missing negatives)        — after WO-3, before WO-5
WO-5 (Q-025 circle-FFT Ligero)      — after WO-4; re-pins everything
WO-6 (P4c masking, Q-015)           — after WO-5 green probe
WO-7 (hardening batch)              — anytime after WO-2
WO-8 (TS13-2 presentation layer)    — anytime, own worktree (SDK-only)
WO-9 (TS13-3 parameterization)      — after WO-5 (it re-pins anyway)
WO-10 (TS13-1 revocation)           — after WO-5 AND decision D-3
WO-11 (TS13-4 issuer privacy)       — PARKED until decision D-4
Decisions D-1..D-6                  — Lucas/architect, not agent work
```

Already DONE, do not redo: Q-025's blind_claim C-fix (verifier requires
`blind_claim == Fp::ZERO` at `ligero.rs:499-501` and `:723-725`; commit-time
prefix-sum zeroing at `ligero.rs:201-205`; negative
`claim_batch_rejects_compensated_value_tamper` at `ligero.rs:975`). Parity
Phases 1–3 (all WOs closed; rayon deadlock fixed; blowup-1 measured-and-rejected).
GKR-v2 parked at `spike/gkr-v2@1847bc06`, reopener = Q-026 — do not touch.

---

## WO-0 — Q-021 MAC landing: gate evidence (verification only, no code)

The Q-021 MAC circuit landed as `9e1ac686` + `c0fda63a`, but the merge-plan M6
step-1 gates have NO logged evidence. Produce it.

1. Main checkout, clean tree at `9e1ac686` or later. Run:
   ```
   rtk proxy cargo test -p eu-id-ec-coprocessor
   rtk proxy cargo test -p eu-id-prover --test mdoc_support
   rtk proxy cargo test -p eu-id-prover --lib
   RAYON_NUM_THREADS=1 rtk proxy cargo run --release --example mdoc_perf_probe
   ```
2. From the probe JSON record: total prove ms, per-phase (encode/commit/
   sumcheck/claim/**mac**), peak RSS, proof bytes, coprocessor bundle bytes.
   Reference checkpoint (todo.md "Q024 row-group P4b checkpoint"): prove
   4,454 ms, rs_encode 2,811 ms, claim 240 ms, MAC 49 ms, proof 5,261,401 B,
   bundle 3,288,727 B, RSS ~451 MB. MAC gate: ≤ 300 ms (expect ≈49).
3. Confirm the three-way KAT (M31 == coprocessor == reference, vector in the
   Q-021 addendum) exists as a test — grep `eu-id-ec-coprocessor/tests/mac.rs`
   and `tests/ecdsa_circuit.rs` for it. If it does NOT exist: STOP + mailbox
   (it was a pre-commit gate; its absence must be dispositioned, not patched
   silently).
4. Confirm the `N_k ≤ 504` / `Q_BITS = 8` assertions exist (grep `504` and
   `Q_BITS` in the coprocessor crate).
5. Append a dated close-out block to `tasks/todo.md` with all numbers + test
   names. Red anywhere ⇒ STOP + mailbox.

---

## WO-1 — Merge `fix/mdoc-sdk-predicate-binding` (M6 step 2)

Branch `fix/mdoc-sdk-predicate-binding @ 4eff9e20` (based `c0fda63a`), worktree
already exists. Closes audit `tasks/audits/2026-07-06-mdoc-sdk-predicate-bypass.md`
C1 (verifier accepts unrequested predicate mode) + C2 (prover-chosen
`element_identifier` substitution).

1. In the MAIN checkout:
   `rtk git merge --no-ff fix/mdoc-sdk-predicate-binding -m "merge: mdoc SDK predicate/statement caller binding (C1/C2)"`.
2. Expected conflicts (both sides touch them since the MAC landing):
   `crates/sdk/src/lib.rs` (verify path near `verify_mdoc_pid`, `lib.rs:658`)
   and `crates/eu-id-prover/src/mdoc.rs`. Resolve textual conflicts ONLY;
   anything semantic (two different verify-path behaviors) ⇒ STOP + mailbox.
   `tasks/**` conflicts: union both sides.
3. Gates (all must be green):
   ```
   rtk cargo build --workspace
   rtk proxy cargo test -p eu-id-sdk        # or: -p sdk — use the crate name in crates/sdk/Cargo.toml
   rtk proxy cargo test -p eu-id-prover --test mdoc_support
   ```
   Then verify the branch's tests exist and pass post-merge: C1 attack negative
   (age predicate index = None + tampered `min_age_years` ⇒ reject), C2
   element-substitution negative, honest age / nat / And positives. Grep the
   sdk crate tests for them; if the merge dropped any, STOP.
4. Update the status line in
   `tasks/audits/2026-07-06-mdoc-sdk-predicate-bypass.md` (C1/C2 → CLOSED,
   merge commit hash).

---

## WO-2 — Merge `fix/froot-pinning-complete` (M6 step 3, closes F-ROOT CRITICAL)

Branch `fix/froot-pinning-complete @ e9676389` (stacked on `e221b0fc` =
`c0fda63a` + air-core pin), worktree exists. F-ROOT: verifier absorbs the
prover's preprocessed root unpinned ⇒ forgeable tables/schedules/constants.

1. Merge onto the post-WO-1 tip:
   `rtk git merge --no-ff fix/froot-pinning-complete -m "merge: pin preprocessed roots at all verifier absorb sites (F-ROOT)"`.
   Expected conflict-free (disjoint crates from WO-1); code conflict ⇒ STOP.
2. Post-merge assertions — all four audited absorb sites pinned or explicitly
   dispositioned in the diff:
   - `crates/air-core/src/lib.rs:469`
   - `crates/stwo-p256/src/proof/mod.rs:2764`
   - hinted_mul `air.rs:1225`
   - `gkr_spike.rs:369/456/547` (feature-gated; check with
     `rtk cargo check -p eu-id-prover --features gkr-spike` — confirm the
     feature name against Cargo.toml first)
3. Gates: tamper-root negative per site (branch ships them — verify present +
   green), plus touched-crate suites:
   ```
   rtk proxy cargo test -p eu-id-air-core   # confirm crate names via Cargo.toml
   rtk proxy cargo test -p stwo-p256
   rtk proxy cargo test -p eu-id-prover --lib
   ```
4. Flip the F-ROOT row in `tasks/audits/2026-07-05-backend-soundness.md` to
   CLOSED with the merge commit hash. Also note: with F-ROOT closed, the
   memory item `project_p256_preprocessed_unpinned` is closed — say so in the
   report.

---

## WO-3 — A-004 window-offset re-binding (PROMOTION GATE — blocks everything mdoc)

Two `#[ignore]` real-prover negatives FAIL on committed code (regressed at
`7fd709aa` "reduce P4b coprocessor public projection", which removed the
element-id offset binding while tests from `f286d3c9` still expect it):

```
RAYON_NUM_THREADS=1 rtk proxy cargo test --release -p eu-id-prover -- --ignored \
  mdoc_window_bind_offset_tampers_reject \
  shared_sha_table_mdoc_digest_and_field_swaps_reject
```

Failure mode today: "D1 element-id offset tamper unexpectedly verified"
(`mdoc.rs:~3743`).

1. Read `tasks/mdoc-mailbox/answers/A-004-mdoc-window-offset-soundness-regression.md`
   in full, then `git show 7fd709aa` to see exactly which public projection was
   removed.
2. Fix per A-004's prescription: re-bind the element-id (and value) window
   **OFFSET** — not just the window bytes — to its CBOR key. Work sites:
   `crates/eu-id-prover/src/mdoc_window_bind.rs` (bind component) and
   `crates/eu-id-prover/src/mdoc.rs` (prover `MdocWindowBind::new_for_attributes`
   at `:534`, verifier `verifier_for_attributes` at `:3779`, attribute loops
   `:3686-3690` / `:3743-3779`). The anchoring pattern to copy is the
   validity-window one: anchor-bytes search + offset fields
   (`mdoc.rs:2745-2781`, fields `mso_valid_*_anchor_offset` at `:2385-2392`).
3. Constraint changes must respect the degree rule D≤3 (log_size+1). If the
   binding needs a new public input or grows the statement: allowed, but name
   the byte delta in the report.
4. Gates: the two negatives above PASS; the honest mdoc profile still proves
   (`isolated_mdoc_circuit_profile_proves_and_verifies --release -- --ignored`);
   full `--test mdoc_support` suite green; report prove-ms delta from the probe
   (gate: no regression > 5%).
5. Do NOT weaken the tests. If the fix genuinely requires protocol-byte changes
   beyond re-binding (fixture re-pin), STOP + mailbox first — WO-5 re-pins
   anyway and the architect may fold them.

---

## WO-4 — P4b missing negatives (10 tests from Q-010/Q-012)

Test-only, transcript-preserving. Existing coverage: tag tamper
(`mdoc_p4b_bundle_accepts_honest_mac_tags_and_rejects_tag_tamper`), spliced
batch entry, `mdoc_coprocessor_rejects_required_negative_mutations` (covers
device_z_mismatch / cross_slot_z_swap / cross_signature_swap / replay /
mac_{tag,claim,consumer_claim}_tamper), non-boolean x bit, q-quotient tamper,
internal-wire tamper. Implement the TEN missing ones (names are canonical —
use them):

Target files: `crates/eu-id-ec-coprocessor/tests/mac.rs`,
`crates/eu-id-ec-coprocessor/tests/ecdsa_circuit.rs`, and the mdoc test module
in `crates/eu-id-prover/src/mdoc.rs` for the LogUp-side ones. MAC primitives:
`crates/eu-id-ec-coprocessor/src/mac.rs` (`gf128_tag:7`, `xor_128:10`,
`gf128_mul:15`); binding state: `crates/eu-id-prover/src/mdoc_mac.rs`
(`MdocMacBind:85-96`, `mix_av_and_tags:884-898`); MAC values:
`ecdsa.rs mdoc_p4b_mac_values:2004` (6 halves: issuer_z lo/hi, device_qx lo/hi,
device_qy lo/hi).

1. `key_share_tamper` — mutate `a_p,i` after `a_v` is fixed ⇒ verifier reject
   via challenge divergence.
2. `layout_tag_tamper` — alter z-vector column indices/length in the layout
   tag ⇒ reject.
3. `per_side_bit_consistency` — bits MAC correctly but no longer recompose to
   the native representation ⇒ reject (coprocessor side).
4. `cross_field_mismatch_issuer_z` — coprocessor witnesses different issuer-z
   bits than the M31 side ⇒ in-circuit MAC check vs shared tags rejects.
5. `a_v_root_absorption_order` — doctored prover derives `a_v` BEFORE the
   commitment root is absorbed ⇒ verifier transcript divergence ⇒ reject.
6. `per_side_bit_consistency_logup` — M31-side variant of (3): LogUp imbalance
   ⇒ "claimed sums do not cancel".
7. `logup_balance_multiplicity` — tamper a provider multiplicity ⇒ same
   rejection.
8. `structural_law_guard` — assert the tree-3 segment emits ZERO relation
   terms (protects the integration law; this is a positive structural pin).
9. `fork_rejoin_placement_mutation` — re-run the Q-012 placement-mutation
   drill (steps 5–8 of its recipe) as a permanent test.
10. `a_p_freshness_linkability` — two proofs over the SAME witness share no
    common MAC material; tags differ. REQUIRED before any parity-ZK claim
    (WO-6 depends on it).

Each test must demonstrably fail against a deliberately-broken oracle before
being trusted (comment the check you used, then delete the breakage). Gate:
full coprocessor + mdoc suites green; zero changes to non-test code. If a test
CANNOT be written without prover-internals hooks that don't exist, STOP +
mailbox naming the missing hook — do not add public API casually.

---

## WO-5 — Q-025: systematic-by-interpolation circle-FFT Ligero (the prove-time gate)

Everything in `tasks/mdoc-mailbox/answers/Q-025.md` sections "The protocol",
"Gates", "Cost projection" — read it in full first; this WO adds anchors and
order. Baseline to beat: prove 4,454 ms of which rs_encode 2,811 ms; target
**~1.75–1.9 s** total, rs_encode ~100–110 ms.

Spike source: worktree `.claude/worktrees/circle-fft-spike`
(branch `spike/circle-fft @ fb3cf59f`), file
`crates/eu-id-ec-coprocessor/src/circle_fft.rs` — verify the worktree's base
commit before porting. Main-tree work sites:
`crates/eu-id-ec-coprocessor/src/ligero.rs` (params `:9-16`, `validate():77`,
`soundness_error():106`, `v2_ligero_params():129`, commit
`commit_witness_profiled:160-210`, claim batch `:330-360`,
`verify_split_claim_batch:467`, `verify_claim_batch:699`),
`src/channel.rs` (`draw_fp:22-31`), `src/ecdsa.rs` (proximity transcript
`:1471-1505`).

Order of operations:

1. **Port + parametrize the FFT.** Copy `circle_fft.rs` into the main crate;
   make `fft/ifft/tables` LOG_N-parametrized for LOG_N ∈ {8, 11}
   (spike hard-codes `CIRCLE_CODEWORD_LEN=2048`/`LOG_N=11` at `:28-29`;
   `circle_evaluate` hard-codes `LOG_N-1` at `:292`). Bring the spike's five
   unit tests along; keep `bench_circle_vs_finite_difference` as `#[ignore]`.
2. **Setup objects.** D256 = size-256 canonic domain (generator order 512, own
   twiddles). `S_data` = 64 fixed natural-order slots of D256. Precompute
   M64⁻¹ (64×64 interpolation inverse for F_64 on S_data). Setup asserts (all
   from Q-025 Gates): D256 ∩ D2048 = ∅ via order check; M64⁻¹ invertible
   (if singular: slide the window deterministically); generator-order asserts
   kept. All deterministic, cached like the spike's `tables()`.
3. **Params fork.** New constructor (e.g. `v3_circle_params()`):
   `row_len: 64, degree_bound: 256, codeword_len: 2048, openings: 170,
   proximity_radius: 862`, plus a claim degree bound of **322** (Q-025's
   F_64×F_256 → F_322 derivation — do NOT reuse `k + row_len − 1`). Fork
   `validate()`/`soundness_error()` accordingly; soundness recomputation to
   record in the ledger: (1−862/2048)^170 ≈ 2^−134 total.
   **Add a params/protocol version tag and absorb it + committed_len into the
   proximity transcript** (`ecdsa.rs:1471-1505`) — this simultaneously closes
   audit item F-PARAMS (LOW) from `tasks/audits/2026-07-05-backend-soundness.md`;
   flip that row when done.
4. **Commit path** (`commit_witness_profiled`): per witness row — 64 data
   values into S_data slots + **192** `pads.draw_fp()` into the remaining D256
   slots (pad budget 170 → 192; same pads channel; Q-024 group-B rule applies
   verbatim: group-B rows encode through this same randomized path) → IFFT256
   → zero-pad to 2048 → circle_fft → codeword. Proximity mask row: 256 random
   coefficients (as spike). Claim blind row: 322 random coefficients, then
   adjust c_0 by −σ/64 so Σ_{s∈S_data} blind(s) = 0 (b_0 ≡ 1).
5. **Proximity check:** unchanged shape — prover sends combined COEFFICIENTS
   (length 256), verifier checks `circle_evaluate(combined, i)` against the
   γ-combined opened symbols.
6. **Claim batch:**
   - Prover: Q = blind + Σ_r W_r·R_r computed in value space on D2048
     (`Q_cw = blind_cw + Σ circle_fft(pad(M64⁻¹·ω_r)) ∘ R_cw_r`), then
     circle_ifft → take `[..322]` → **assert `[322..]` all zero** (tail-zero
     gate). `batched_row_weights` unchanged. **DELETE the `blind_claim` field**
     (`ligero.rs:54`) and every use (`:344-351`, `:499-501`, `:723-725`) —
     this is the version bump Q-025 authorizes the deletion at.
   - Verifier per opened column i:
     `circle_evaluate(batch.coefficients, i) == blind_symbol(i) + Σ_live_r
     circle_evaluate(w_coeffs_r, i) · column[r]`; verifier computes each
     `w_coeffs_r = M64⁻¹·ω_r` once per batch. Fix BOTH `verify_claim_batch`
     and `verify_split_claim_batch` (split path: same shape across the two
     groups).
   - q_sum replacement: `Σ_{s∈S_data} circle_evaluate_at_point(coeffs, s) ==
     Σ_c γ_c·value_c` — add a `circle_evaluate_at_point` variant taking an
     explicit (x, y), since S_data ⊄ D2048.
7. **Q-019 items verbatim:** params version tag (done in 3); KAT regeneration
   (new Merkle roots/proof bytes); FULL negative-suite rerun — including all
   WO-4 tests and `claim_batch_rejects_compensated_value_tamper` re-expressed
   for the deleted-field protocol (value tamper with no compensation channel
   must reject); transcript-order tests rerun; NEW fixture pin — grep for the
   pinned proof-byte constants (search `5261401` / `proof_bytes` asserts in
   `crates/eu-id-prover`); if no byte-pin test exists, CREATE one now (pin the
   probe's proof bytes + root), don't just update numbers in todo.md.
8. **Round-trip gate:** IFFT256 → pad → FFT2048 → circle_evaluate agrees at 5
   random columns AND all 64 S_data points.
9. **Report:** probe JSON leading with prove ms (encode/commit/sumcheck/claim
   + MAC) + peak RSS, single-thread, plus claim-inventory counts and the
   soundness-ledger update. Verify ms informational only (Q-024 re-weight:
   prove + RSS are the gates).
10. **Pre-approved descents (do NOT improvise beyond these):** (a) singular
    S_data window → slide it; (b) tail-zero assert trips → widen claim bound
    to measured support +2, re-derive e, REPORT the new number; (c) anything
    else → STOP + mailbox with the failing check.

---

## WO-6 — P4c masking (Q-015 treatment classes) — after WO-5 green

Read `tasks/mdoc-mailbox/answers/Q-015.md`,
`tasks/audits/2026-07-06-p4c-degree-inventory.md`, and
`tasks/p4c-masking-note.md` in full first. Naive `×is_active` gating is NO-GO
(17 SHA constraint families at D=3). Implement per class:

- **Class A** (PublicDigestBind, MdocValidityBind, MdocWindowBind,
  MacBindingEval, bridge DigestBindEval): drop or selector-re-gate the
  `(1−active)·value = 0` zero-pins; bump log 4/5 → 9 for 256 blind rows; all
  must land ≤ D3.
- **Class B** (Sha256Eval ×4 mdoc, MacConsumerEval): decoy-computation
  blinding — pad region filled with an HONEST computation on fresh random
  inputs (valid SHA trace on a random message; valid MAC ladder on random
  bits) with `enabler = 0`. Zero constraint/degree changes. Specific edits:
  rewrite `mdoc_mac.rs:541` in selector-weighted form; drop the ap/s/post
  zero-pins at `mdoc_mac.rs:478, 481, 486, 492`; **DO NOT TOUCH
  `mdoc_mac.rs:516-518`** (already deg-3, preprocessed-gated) — add a degree
  pin test for it. Pin MacConsumer's 256 slack with a test.
- **Class C** (AgeRangeCheck, NationalityEval): structural rewrite to
  1-active-row + preprocessed selector, then treat as Class A. Re-run age/nat
  negatives.
- **Class D** (SHA split-pack ×8, Range_16, table producers): extend domain
  +1 log for dummy-key regions with intra-component cancelling emits
  `±m/(z−dummy)`. Cost budget: SHA tables 2^16→2^17 ≈ +0.22 s prove.
- **Class E**: blinder tuple pairs for the published claimed sums in proof
  serialization.

Required tests (all from Q-015): full suite green with decoy padding ON;
MacConsumer 256-slack pin; degree pin for `mdoc_mac.rs:516-518`; dummy-key
region negatives (honest consumer emitting reserved key ⇒ reject; imbalance ⇒
reject); Class-C age/nat negatives rerun; the Case-2 character-sum
verification from the masking note; and WO-4 test #10
(`a_p_freshness_linkability`) green — both are hard gates before ANY
parity-ZK claim.

Deliverable beyond code: the masking table (per module: treatment class,
per-column blinding status, witness-at-opening leakage, remaining
assumptions — including the generic-position assumption on the 192 pad values
from Q-025's hiding note, added explicitly). Budget gate: prove delta
≤ +0.25–0.35 s on the WO-5 baseline; report the measured number.

---

## WO-7 — Hardening batch (audit 2026-07-05, non-CRITICAL rows)

Independent small fixes; one commit each; flip each ledger row in
`tasks/audits/2026-07-05-backend-soundness.md` with the commit hash.

1. **F-BENCH (HIGH, honesty):** `longfellow_equiv.rs:38-41` runs the 13-bit
   default config but perf-log labels it "128-bit". Fix the bench to run the
   config it claims (or relabel), regenerate the affected perf-log rows,
   annotate superseded rows — do not silently rewrite history.
2. **F-BIAS (MED):** `crates/eu-id-ec-coprocessor/src/field.rs:46-53` —
   `Fp::random` single conditional subtraction ⇒ ~2^−32 bias/draw. Replace
   with rejection sampling (loop until < p). Deterministic tests that pinned
   draw sequences will shift: re-pin them, count them in the report.
3. **F-SUM (LOW):** `stwo-sha256 multiplicities.rs sum_multiplicity_vectors` —
   unchecked `u32 +=` can wrap in release. Use `checked_add` +
   panic-with-context (completeness guard, not soundness).
4. **F-PARAMS (LOW):** closed inside WO-5 step 3 — verify, don't duplicate.

---

## WO-8 — TS13-2: presentation-layer conformance (SDK-only, own worktree, start anytime)

Read `tasks/eudi-ts13-conformance-gaps.md` WO-TS13-2 first. No circuit change;
branch from the post-WO-1 tip (needs the caller-binding surface).

1. New `crates/sdk/src/presentation.rs`: `ZkRequest` (DeviceRequest.requestInfo
   parameter) parse/emit; `ZkDocument` / `ZkDocumentData(Bytes)` (tag #6.24)
   for `DeviceResponse` — doctype, zkSystemId, timestamp, disclosed
   (name,value) pairs, proof bytes. CBOR via the already-present `ciborium`
   0.2.2 (`crates/sdk/Cargo.toml:41`); copy the parsing idioms from
   `mdoc.rs` (`value_int_key:2067`, `x5chain_certificates:2091`).
2. OpenID4VP DCQL binding: format `mso_mdoc_zk` with `meta.zk_system_type`
   entries `{zkSystemId, system: "longfellow-libzk-v1", params:{circuit_hash}}`;
   parse-and-reject `zk-jwt` as unsupported; zk-jwt response encoding
   documented as `base64url(JSON header).base64url(proof)` for the reserved
   path.
3. `circuit_hash` = SHA-256 of the canonical circuit/config fingerprint.
   Source it from `fingerprint_preprocessed_columns`
   (`crates/air-core/src/lib.rs:125`) + the pinned PcsConfig; wire validation
   into `verify_mdoc_pid` (`crates/sdk/src/lib.rs:658`, right after
   `MdocProofEnvelope` deserialization ~`:663`): request/proof with
   circuit_hash ≠ the pinned fingerprint for its parameterization ⇒ reject,
   fail-closed, no fallback. (Full per-tuple hash family arrives with WO-9;
   here, one hash for the current 2-attr PID circuit is sufficient and the
   API must already take the hash as input.)
4. Gates: byte round-trip fixtures against the JSON/CDDL examples quoted in
   TS13 (the age_over_18 mDL example, circuit_hash `f88a39e5…`); unknown
   circuit_hash ⇒ reject; unknown zkSystemId ⇒ reject; rerun the WO-1
   caller-binding negatives against the new entry points; existing
   `verify_rejects_statement_envelope_drift` (`sdk/src/lib.rs:921`) family
   still green.

---

## WO-9 — TS13-3: circuit parameterization family + published circuit_hash (after WO-5)

Subsumes the old "N-attribute" plan item.

1. Generalize `MDOC_MAX_DISCLOSED_ATTRIBUTES` (currently hard-wired 4 at
   `crates/eu-id-prover/src/mdoc_window_bind.rs:43`) into a compile-tuple
   parameter (max doc bytes, #attributes, max attr size, #potential issuers).
   Every dependent site must be swept: `mdoc_window_bind.rs:54, 56, 105, 138,
   160, 247, 252, 398, 405` and the validation at `mdoc.rs:190-192`
   (`UnsupportedAttributeCount`). One compiled/pinned circuit per supported
   tuple; start with exactly two tuples: 1-attr age_over_18 mDL (the Age
   Verification pilot) + the current 2-attr PID.
2. Emit + golden-file the circuit_hash per tuple (consumed by WO-8 step 3).
   Changing ANY pinned param ⇒ new hash ⇒ new golden file — same discipline as
   byte-pins.
3. Soundness documentation gate: one table of composed-system statistical
   soundness bits per tuple (Ligero 2^−134 post-WO-5 + sumcheck + FS
   accounting); ≥ 100 bits required per TS13 §3.
4. Gates: both tuples prove+verify honest vectors; cross-tuple proof
   (1-attr proof against 2-attr verifier and vice versa) ⇒ reject via
   circuit_hash; full mdoc suite + WO-4 negatives green per tuple; prove-ms
   per tuple reported.

---

## WO-10 — TS13-1: ZK non-revocation (after WO-5; BLOCKED on decision D-3)

Read `tasks/eudi-ts13-conformance-gaps.md` WO-TS13-1 first — the mechanism
(sorted-pair signatures over consecutive revoked ids + epoch) and both STOPs
are specified there. Anchors for the implementing agent:

1. New instance kind alongside issuer/device: extend
   `implemented_circuit_instances` (`crates/eu-id-ec-coprocessor/src/ecdsa.rs:3220`,
   vec at `:3227`) and `implemented_circuit_verifier_instances` (`:3286`);
   sweep the instance loops at `:534, :548, :728, :869` (prover) and
   `:1008, :1013` (verifier). One more ECDSA verify with
   e = SHA-256(encode(id_lo ‖ id_hi ‖ ep)) (8-byte LE ids + 4-byte LE epoch,
   DER-free sig, per spec example).
2. MAC binding: extend `mdoc_p4b_mac_values` (`ecdsa.rs:2004-2015`) from
   `[Gf128; 6]` to 8 halves (+revocation e lo/hi), and the corresponding
   `MACS_PER_PROOF` row plumbing in `crates/eu-id-prover/src/mdoc_mac.rs`.
3. Range legs `id_lo < id < id_hi`: byte-decomposed comparisons on the M31
   side reusing the validity-window comparison pattern (`mdoc.rs:2745-2781`
   anchor+offset machinery); id/id_lo/id_hi bytes MAC-bound into the
   pair-message window and the credential-id window.
4. Public statement: + rpk, ep. SDK verify derives BOTH from the caller's
   request (trust list), never the envelope — same rule WO-1 enforces.
5. STOP-1 (before wiring): confirm the spec's sentinel convention for
   id < id_1 / id > id_n against the published example; ambiguous ⇒ mailbox.
   STOP-2 = decision D-3 (below) — do not start step 2+ without it.
6. Gates: honest non-revoked proof verifies; revoked id (id == some id_i) has
   no satisfying witness (prover-side construction fails); forged pair-sig /
   out-of-range pair / stale ep ⇒ verifier reject; named prove-ms + RSS delta
   (expect ≈ +1 ECDSA instance + 2 MAC halves).

---

## WO-11 — TS13-4: in-circuit Access-CA verification — PARKED

Do not start without decision D-4. Scope stays as written in
`tasks/eudi-ts13-conformance-gaps.md` WO-TS13-4 (ipk → witness; +1 ECDSA
verify of the DS cert by the public ACA/IACA key over SHA-256(TBSCertificate);
TBS parsing windows via the same anchoring machinery).

---

## Decisions required (Lucas / architect — agents must not decide these)

- **D-1 — 96-bit vs 128-bit** (re-posed 2026-07-03): (a) keep 96-bit → pow 10
  + 43q, proof +13%; (b) 128-bit to match Longfellow → pow 10 + 59q, proof
  ~+50%, honest like-for-like parity claims. Blocks the WO-3.0 redo (original
  `82e3fa63` targeted main's file; must be redone against this branch either
  way).
- **D-2 — M-A3 SHA-floor path:** S1-B1 tie-back verdict is UNSOUND
  (global-bound MLE vs stwo lifted-domain bounds; remedies out of scope).
  Choose: GKR rollout WO if upstream stwo fixes global-lift, or content-aware
  table redesign (architect-scoped). WO-2.1 mechanical merge is DEAD (Q-008:
  table contents differ).
- **D-3 — credential-id location for revocation** (TS13 STOP-2): (a) dedicated
  signed attribute (spec-cleanest, needs issuer cooperation) vs (b) derived
  id = SHA-256(IssuerAuth signature bytes) (no issuance changes). Blocks WO-10.
- **D-4 — TS13-4 go/no-go** (issuer herd privacy; changes public statement +
  trust model).
- **D-5 — V1 public-statement caveat sign-off:** shipping posture with public
  z/r/s linkability caveat (WO-M1 Phase 4) — already ACKed once (Q-M1-003);
  confirm it survives the P4c landing or is retired by it.
- **D-6 — stale merge-plan phases M2/M3:** `codex/full-mdoc-plan` and
  `s4-lite` worktrees were dirty at the 2026-07-04 window (merges skipped).
  Decide: quiesce + rerun merge-plan M2/M3, or abandon those branches.
  (`wo30-128bit` landed via WO-0-rebaseline; `spike/gkr-v2` stays parked.)

## Explicitly NOT remaining (verified done, for the record)

- Q-025 blind_claim C-fix + compensating-tamper negative (on main since the
  MAC landing).
- Parity Phases 1–3: all WOs closed; rayon deadlock fixed (3×30 min soaks);
  provider dedup −2.64 M cells landed; blowup-1 measured and REJECTED;
  identity_e2e bench live. Current headline (1-thread): SHA-1 327 ms /
  SHA-33 424 ms / mdoc 996 ms / pipeline 12-core 1.194 s.
- ECDSA mobile parity: formally closed INFEASIBLE (S2-R + S3 NO-GO); Path A is
  the plan of record.
