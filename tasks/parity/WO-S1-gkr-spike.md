# WO-S1 — GKR spike: port ONE SHA-256 lookup table to stwo's GKR LogUp

**Plan ref:** longfellow-parity-plan.md § 4.1. **Timebox: 1 week.** Everything behind a new `gkr-spike` cargo feature in `stwo-sha256`, `air-core`, `eu-id-prover` — the default path stays bit-identical (CI proof-vector tests must pass with the feature off).

## Goal + success metric
Replace the committed LogUp interaction columns of exactly one lookup relation with stwo's GKR lookup argument, measure, report. Success = a working prove+verify round-trip with the feature on, plus a filled-in report table (below). Metrics of record:
- **Time:** single-thread `longfellow_equiv_sha/BM_ShaZK_equiv/1/prove` (and `/verify`) delta, feature off vs on. Bench name built at `crates/eu-id-prover/benches/common/longfellow_equiv.rs:44,57`.
- **Cells:** committed-cell delta via shape_dump (`crates/eu-id-prover/src/shape_dump.rs:35`, run line in its docstring at `:4`).
- **Proof size:** serialized proof bytes delta (GkrBatchProof is additive; interaction columns removed are subtractive).

## Target: the `xor_8` table (simplest — one relation, one consumer component)
| What | Where |
|---|---|
| Table component | `Xor8Eval`, `crates/stwo-sha256/src/components.rs:429` (`Xor8Component` = `FrameworkComponent<Xor8Eval>`, `:459`) |
| Relation | `Xor8Relation` (width-3 tuple `(x, y, x⊕y)`), `crates/stwo-sha256/src/relations.rs:137`; field `Sha256Relations.xor_8` at `:433`, drawn at `:459` |
| Preprocessed table | 3 cols @ log 16, built by `build_xor_8_table` — `crates/stwo-sha256/src/preprocessed.rs:102,175-178` (LOG_SIZE_16 = `preprocessed.rs:62`) |
| Multiplicities | `xor_8_multiplicities(witness) -> Vec<u32>`, `crates/stwo-sha256/src/multiplicities.rs:167` (sanity test `:454`) |
| Consumer (only one) | main `Sha256Eval` — 4 chunk-wise emits in `crates/stwo-sha256/src/constraints.rs:335,344,459,468`, via the helper doc'd at `:1260-1348` |
| Interaction writer / claim | `crates/stwo-sha256/src/interaction.rs` — `ComponentClaim xor_8` at `:126`, summed `:142`, mixed `:164` |
| Component instantiation | `crates/stwo-sha256/src/air.rs:630,684`; table-side interaction col count at `air.rs:598-599` (1 lookup → 4 SecureField cols @ log 16) |

Today's xor_8 committed footprint: table side = 4 interaction cols @ log 16 (≈1.05 M M31 cells) + 1 multiplicity col @ log 16; consumer side = its share of Sha256Eval's batched interaction cols (4 emits). The spike removes the interaction cells; multiplicity + preprocessed table stay committed.

## stwo API facts (all in `/Users/lucas/.cargo/git/checkouts/stwo-59e22971a65c0edb/16cd2f9/`)
- **Prover:** `pub fn prove_batch<B: GkrOps>(channel, input_layer_by_instance: Vec<Layer<B>>) -> (GkrBatchProof, GkrArtifact)` — `crates/stwo/src/prover/lookups/gkr_prover.rs:401`. Doc comment: *"The input layers should be committed to the channel before calling this function."*
- **Layer kinds** (`gkr_prover.rs:100` area): `GrandProduct`, `LogUpGeneric {numerators, denominators}`, `LogUpMultiplicities {numerators: Mle<BaseField>, denominators}`, `LogUpSingles {denominators}`. Table side = `LogUpMultiplicities` (numerators = the u32 multiplicity column as BaseField MLE); consumer side = `LogUpSingles` (numerator ≡ 1).
- **Verifier:** `pub fn partially_verify_batch(gate_by_instance: Vec<Gate>, proof: &GkrBatchProof, channel) -> Result<GkrArtifact, GkrError>` — `crates/stwo/src/prover/lookups/gkr_verifier.rs:17`. `GkrBatchProof {sumcheck_proofs, layer_masks_by_instance, output_claims_by_instance}` at `:152`; `GkrArtifact` (OOD point + claimed input-layer evals) at `:162`; `Gate` enum at `:180`. *Partial* = the input-layer MLE claims in the artifact are NOT checked there — you must check them against the STARK.
- **Tying claims into the STARK:** the xor example's `MleEvalProverComponent` (`crates/examples/src/xor/gkr_lookups/mle_eval.rs:48`, `::generate` at `:75`) + `MleEvalVerifierComponent` (`:302`) + `eval_mle_eval_constraints` (`:459`) prove "committed column C evaluates to claim v at OOD point p" as an AIR component (eq-evals column + prefix-sum). Multiple MLE claims at the same n_variables are RLC-combined via `MleCollection::random_linear_combine_by_n_variables` (`accumulation.rs:21,39`). Preprocessed-table MLEs (our xor table) don't need committing at all in the example — the verifier evaluates them succinctly (`gkr_lookups/mod.rs:54` `eval(mle_evals, p)` pattern); for the spike we may instead keep the committed table and add its columns to the mle_eval claims (simpler, still sound).
- **Fiat-Shamir per GKR layer** (prover and verifier symmetric, in `prove_batch`/`partially_verify_batch`): mix output/layer claims (`channel.mix_felts`), draw `sumcheck_alpha` + `instance_lambda`, run sumcheck rounds (each round mixes the round poly, draws a challenge), locally evaluate the gate, mix layer masks. You only choose where the whole GKR block sits in OUR transcript; internal ordering is fixed by stwo.

## Port plan (feature `gkr-spike`)
1. Add `gkr-spike = []` to `crates/stwo-sha256/Cargo.toml` `[features]` (line 6) and plumb through `air-core` and `eu-id-prover` features (both have `[features]` at line 6 of their Cargo.toml).
2. New module `crates/stwo-sha256/src/gkr_spike.rs` (gated `#[cfg(feature = "gkr-spike")]`): builders that produce (a) the table-side `Layer::LogUpMultiplicities` from `xor_8_multiplicities()` output + denominators `z0 + z1·x + z2·y + z3·(x⊕y)` combined with the drawn `Xor8Relation`, and (b) the consumer-side `Layer::LogUpSingles` from the 4 chunk-emit tuples (recompute the same values the emits at `constraints.rs:335,344,459,468` use, as an MLE of length = consumer trace size padded to a power of two — padding rows must contribute fraction 0; see soundness #4).
3. Under the feature, make the Sha256 module's `write_interaction` (`air-core` trait, `lib.rs:150`) skip the xor_8 fractions: remove the 4 table-side cols and drop the xor_8 terms from the consumer's batched columns (in `interaction.rs`; xor_8 claim plumbing at `:126,142,164`). Keep the multiplicity column in tree 1 (it feeds the GKR numerators AND stays committed = binding).
4. Under the feature, remove the LogUp `add_to_relation` calls for xor_8 in `Xor8Eval::evaluate` (`components.rs:434`) and the 4 consumer emits — but keep all non-lookup constraints. The claimed-sum cancellation check in `air-core` `verify()` must exclude xor_8's claim under the feature (it summed to the global zero check — see `lib.rs` verify body; today "LogUp claimed sums do not cancel" gate).
5. Orchestration (`crates/air-core/src/lib.rs`, `prove()` at `:159`): insert the GKR phase AFTER tree 2 commit (`:216-223`) — at that point all inputs to the GKR layers (multiplicity col in tree 1 at `:204-208`, relation randomness drawn after tree 1) are already channel-committed, satisfying prove_batch's precondition. Call `prove_batch` with the two layers; the returned `GkrBatchProof` rides in a new field of the proof struct (feature-gated), `GkrArtifact` feeds step 6.
6. Tie-back: instantiate `MleEvalProverComponent::generate` (or a vendored copy — the example lives in `crates/examples`, not the library; see Risks) for the input-layer columns that are committed (multiplicity, and consumer tuple columns if you route them from committed trace cols via a `MleCoeffColumnOracle`). Its trace goes in a NEW tree committed after the GKR phase (channel order: GKR proof messages already mixed by prove_batch → commit mle_eval tree). For the preprocessed xor table columns, verifier evaluates the table MLE succinctly (closed form for (x,y,x⊕y) grids, cf. `gkr_lookups/mod.rs:54` pattern) — or, fallback, add them to the mle_eval claims.
7. Verifier (`air-core` `verify()` at `:243`): after the tree-2 commit replay (`:258` area), run `partially_verify_batch` with matching `Gate`s, check `output_claims_by_instance` satisfy: sum(table fractions) = sum(consumer fractions) (the LogUp balance, replacing the removed claimed-sum terms), then verify the artifact's input-layer claims via `MleEvalVerifierComponent` + succinct table eval at `artifact.ood_point`.
8. Wire the eu-id-prover proof struct + (de)serialization for the new fields, feature-gated.
9. Tests in `stwo-sha256` (gated): (a) round-trip prove/verify 1-block; (b) negative: corrupt one multiplicity → verify fails; (c) negative: tamper a consumer chunk value → fails; (d) padding rows contribute zero (prove a non-power-of-two consumer count).
10. Run the full workspace test suite with the feature OFF — must be untouched (zero diff in proof bytes; existing pinned-proof tests are the check).
11. Measure (commands below), fill the report table, write findings into this file's Report section.

## Soundness checklist (all must hold with the feature on)
- **Multiplicity correctness:** multiplicity column stays committed in tree 1 and is the same data fed to `Layer::LogUpMultiplicities`; the mle_eval component must bind the GKR input-layer claim to THAT committed column (not a prover-supplied vector). No unchecked hint.
- **Table binding:** the (x, y, x⊕y) denominators must come from the verifier's own succinct evaluation (or committed preprocessed cols), never from prover-supplied claims. NOTE the open CRITICAL (memory `project_p256_preprocessed_unpinned`): `verify()` commits `proof.commitments[0]` with sizes only (`lib.rs:253-258`) — it trusts the prover's preprocessed root. Succinct table eval in the GKR path is actually STRONGER than today's committed table; do not regress it by binding to the untrusted root. State in the report which option you took.
- **Channel ordering:** GKR runs only after every input (multiplicities, relation randomness, consumer trace) is committed/mixed; the verifier replays the identical order. Any new tree commit mixes its root before subsequent draws. Add a transcript-order comment block in `air-core`.
- **Balance check:** the removed xor_8 claimed-sum terms must be replaced by an explicit check that GKR output claims cancel (table side = consumer side). Missing this = unsound (free lookups).
- **Padding:** consumer `LogUpSingles` MLE is a power of two; padding entries must be exact-zero fractions (e.g. numerator 0 via LogUpGeneric, or pad with a dummy tuple counted in multiplicities). Pick one, test it (test 9d).

## Measurement + report
```bash
cargo bench -p eu-id-prover --bench longfellow_equiv_bench -- 'BM_ShaZK_equiv/1/'   # off, then on with --features gkr-spike
cargo test -p eu-id-prover --release shape_dump -- --ignored --nocapture             # off vs on
```
Report table (append to this file): | metric | feature off | feature on | delta | → rows: prove ms (1-thread), verify ms, committed cells total, sha256 interaction cells, proof bytes, GkrBatchProof bytes. Plus 3 lines: extrapolation to all ~23 SHA table components, verifier-cost verdict vs the ≤2x gate (plan § 7), recursion-impact note (fewer committed cols helps Blake2s recursion; sumcheck verify inside recursion is new work — estimate only).

## Report — 2026-07-02

Implementation summary: `gkr-spike` is plumbed through `stwo-sha256`, `air-core`, and `eu-id-prover`; `xor_8` producer interaction columns and 16 consumer lookup sites are skipped under the feature; a 17-instance side GKR proof covers the table and consumer fractions; standalone SHA and combined `eu-id-prover::Proof` serialize the feature-gated GKR wire proof. The GKR proof is verified for output-claim balance and by `partially_verify_batch`.

Soundness status: **S1-A accepted by Q-003 as a mechanics milestone only; S1-B remains required in this WO**. This is a working spike and measurement, not a fully sound replacement. The GKR verifier artifact's input-layer claims are not yet MLE-bound to the committed STARK multiplicity/base-trace columns, and the GKR phase is not yet inserted into the shared `air-core` transcript with a follow-on MLE-eval commitment tree. Table denominators are recomputed from the local `build_xor_8_table()` data, but the current verifier still does not check the artifact claims against committed columns or a succinct table eval.

| metric | feature off | feature on | delta |
|---|---:|---:|---:|
| prove ms (1-thread), `BM_ShaZK_equiv/1/prove` median | 1065.2 ms | 1047.8 ms | -17.4 ms (-1.6%) |
| verify ms, `BM_ShaZK_equiv/1/verify` median | 0.61277 ms | 0.76498 ms | +0.15221 ms (+24.8%) |
| committed cells total, `shape_dump` | 28,488,480 | 28,222,240 | -266,240 |
| sha256 interaction cells, `shape_dump` | 5,800,640 | 5,534,400 | -266,240 |
| standalone SHA proof bytes | 60,045 | 73,749 | +13,704 |
| `xor_8` GKR wire proof bytes | 0 | 18,824 | +18,824 |

Extrapolation to all ~23 SHA table components: the single `xor_8` move removed 266,240 committed cells, but payload grew because this GKR proof is additive and the removed STARK proof bytes are smaller than the side proof. Linear extrapolation is not reliable: larger/merged tables may amortize GKR overhead better, while many independent small GKR instances would likely worsen proof bytes and verifier cost. Per Q-003, this 1-block result mostly confirms the four table-side interaction columns moved; Phase 4's larger prize is moving consumer-side fraction columns in tall components, such as `hinted_mul`'s log13 interaction columns.

Verifier-cost verdict vs the <=2x gate: accepted for spike measurement only. Verify regressed from 0.613 ms to 0.765 ms, still 1.25x feature-off for this table and under the 2x gate, but this excludes the missing MLE tie-back verification work.

Recursion-impact note: fewer committed interaction columns should help Blake2s/Merkle query work in recursion, but the GKR sumcheck verification and future MLE tie-back add new recursive arithmetic. Net recursion impact is ambiguous until the tie-back is implemented and measured.

## S1-B1 attempt — 2026-07-03

Implemented the Q-004 table-side-only shape locally: consumer `xor_8` LogUp remains committed; the producer table interaction columns remain removed; the producer claimed sum is still computed and mixed; a single table-side GKR proof runs after tree 2; the fixed-table denominator claim is verifier-evaluated; and the multiplicity numerator claim is tied back through the vendored MLE-eval component in a new post-interaction tree.

Focused checks passed:
- `cargo check -p stwo-sha256 --features gkr-spike`
- `cargo check -p eu-id-prover --features gkr-spike`
- `cargo test -p stwo-sha256 --features gkr-spike gkr_spike::tests::xor_8_gkr_round_trip_balances_one_block -- --exact --nocapture`
- `cargo test -p stwo-sha256 --features gkr-spike gkr_spike::tests::xor_8_table_denominator_mle_matches_bruteforce_eval -- --exact --nocapture`
- `cargo test -p stwo-sha256 --features gkr-spike gkr_spike::tests::vendored_mle_eval_component_proves_and_verifies_random_mle -- --exact --nocapture`

Final Q-006 verdict: **tie-back-incomplete, stop the spike here**. The bounded symmetry checklist found:
- Prover and verifier both declare the post-interaction log-19 pad column with an empty mask; the pad removes the original lifted-decommit OOB (`len 8192 index 10240`).
- Isolated diagnostics show the same boundary: natural-bound higher-log pad/fourth-tree MLE reproductions fail constraints, while forcing the MLE component to the pad/global bound reaches the pinned-Stwo lifted-domain OOB path (`len 4 index 5` in the small reproduction). These diagnostics are kept as ignored tests.
- The integrated SHA proof still rejects with `Fri(FirstLayerCommitmentInvalid { error: RootMismatch })` under `cargo test -p stwo-sha256 --features gkr-spike --release prove_and_verify_abc -- --exact --ignored --nocapture`.
- The remaining asymmetry is the committed `xor_8` multiplicity oracle sampling: the MLE tie-back needs that polynomial at the MLE component's shifted trace point, but the current framework obtains it through the existing `Xor8Eval` component mask. Re-owning that column in a global-bound component is the multi-day rewrite Q-006 explicitly moved out of this WO.

Integration verdict for Phase 4 pricing: the pinned Stwo rev's PCS assumes per-tree max = global max (pad workaround exists, ~0.5 M cells), and the example MLE-eval component's natural-domain quotient model does not drop into this multi-size proof cleanly. A sound tie-back requires rewriting it as a global-bound FrameworkComponent-style component, or an upstream Stwo change.

## Risks / unknowns (with evidence)
- **`MleEvalProverComponent` is example code, not library API** (`crates/examples/src/xor/gkr_lookups/mle_eval.rs`, 54 KB) — likely needs vendoring into our tree and adapting to our `air-core` Module traits. Biggest unknown of the spike; budget half the week.
- **`Layer::LogUpMultiplicities` has `unimplemented!()` in `try_into_mask`** — `gkr_prover.rs:359` ("Should never get called": the layer converts to LogUpGeneric after one round). Safe for log-16 inputs; would panic only on degenerate ≤1-variable input layers. Don't build tiny test layers of that kind.
- **SIMD backend falls back to CPU for small layers:** `backend/simd/lookups/gkr.rs:59-60` (`n_variables <= LOG_N_LANES` → `to_cpu()`), `:88-89` (`n_terms < N_LANES`). Fine at log 16; only affects the last few GKR layers (cheap).
- **Consumer-side extraction is entangled:** xor_8 fractions are batched with other relations inside Sha256Eval's interaction columns (`interaction.rs`); un-batching just xor_8 may ripple through the pairing logic (`air.rs:589-602` accounting). If ripple is large, acceptable spike shortcut: leave consumer batching intact and GKR only the table side + a consumer-side duplicate emit set — measure both honestly, but flag that only the full move counts for Phase 4.
- **Extra tree / transcript change ⇒ proof format change** even for the gated path — keep it entirely behind the feature; no versioning work (out of scope).
- **Degree/log+1 rule:** mle_eval constraints must respect D≤3 at its log_size (memory `project_p256_degree_bound_rule`); check `eval_mle_eval_constraints` degrees before committing to a tree size.

## Out of scope
All other SHA/P256 tables; the recursion adapter (`crates/eu-id-prover/src/recursive.rs`); proof-format versioning/migration; fixing the preprocessed-root pinning CRITICAL (re-flag it, don't fix); parallel-feature interactions; upstreaming anything to stwo.
