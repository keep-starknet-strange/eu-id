# stwo-p256 — full crate reorganization (design spec)

**Date:** 2026-06-08
**Status:** approved design → ready for implementation planning
**Scope:** `crates/stwo-p256` (≈47k LoC). Structural reorganization + dead-code removal only.

---

## 1. Goal

Turn the crate from a partly-flat layout with two multi-thousand-line monoliths and significant
dead/dormant code into a **clean, consistent, domain-organized module tree** where every AIR component
follows the same `air / trace / interaction` split, the live verifier is the only thing present, and no
file is a monolith.

## 2. Decisions (locked)

1. **Delete everything not live.** Keep only code reachable from the live monolithic path
   (`prove_current_air_monolithic` / `verify_current_air_monolithic`) and the relations folded into
   `relation_balances()`, plus their transitive dependencies and the tests that exercise them.
2. **Reorg first, behavior-identical.** This is a *pure refactor*: relocate and split code, fix
   `mod`/`use`, delete dead code. **No** logic edits, **no** reordering of column reads, constraint
   emissions, relation emissions, or component registration. Proofs remain byte-identical.
3. **Target structure = "A" (domain/pipeline).** See §4.
4. **Soundness fixes (C1/C2/C5/…) are out of scope here** — they land afterwards on the clean base.

## 3. Non-goals

- No constraint/soundness changes (tracked separately in `crates/stwo-p256/docs/soundness-audit.md`).
- No performance optimization.
- No API surface changes beyond module paths (the public `prove`/`verify` entry points keep their
  names; only their module location may change, re-exported from `lib.rs` to preserve external paths
  where practical).

## 4. Target module tree

```
src/
  lib.rs                        # module decls + public re-exports
  types.rs                      # U256 etc. (foundational, kept at root)
  constants.rs                  # P-256 params (shared, kept at root)
  field/                        # Fp arithmetic (mod p)
    mod.rs
    limbs.rs                    # <- limbs.rs
    ops.rs                      # <- field_ops.rs
    solinas/
      mod.rs
      native.rs                 # <- fp_solinas.rs
      air.rs                    # <- fp_solinas_air.rs
  curve/                        # native EC (no AIR)
    mod.rs
    affine.rs                   # <- curve.rs
    projective.rs               # <- projective.rs (rcb_double / rcb_mixed_add)
  range_checks/                 # already clean — moved verbatim
    {mod, component, interaction, trace}.rs
  gadgets/
    mod.rs
    canonical_lt.rs             # <- scalar/canonical_lt.rs (shared LT gadget)
  components/                   # one module per AIR component
    mod.rs
    projective_rcb_mul/         # SPLIT <- projective_air.rs (6.7k)
      {mod, air, trace, interaction, relation}.rs
    public_key_curve/           # <- public_key_curve_air.rs (+ public_key_check.rs as native.rs)
      {mod, air, trace, interaction, native}.rs
    scalar_setup/               # <- setup_air.rs + setup_witness.rs + cert_bind.rs
      {mod, air, trace, witness, cert_bind}.rs
    scalar_mod_mul/             # moved verbatim (already well-split)
      {mod, air/component, trace, interaction, relation, layout, ...}
    public_inputs/              # <- public_inputs.rs
      {mod, air, trace, relation}.rs
    fake_glv/
      mod.rs
      scalar/                   # <- fake_glv_scalar.rs (+ WIP) + fake_glv_decompose.rs
        {mod, air, trace, decompose}.rs
      selector/                 # <- fake_glv_selector.rs + the LIVE operand providers
        {mod, air, trace, signed_operand, direct_operand, lsb_correction}.rs
      chain/                    # <- fake_glv_chain*.rs
        {mod, native, continuity, expansion, schedule}.rs
      ec_source/                # <- fake_glv_ec_source.rs + fake_glv_prepared_point_source.rs
        {mod, air, trace}.rs
      prepared_table/           # SPLIT <- prepared_table.rs (3.7k) + prepared_point.rs
        {mod, air, trace, interaction, point}.rs
    final_add/                  # <- final_add_air.rs
      {mod, air, trace, interaction}.rs
    final_check/                # <- final_check_air.rs + final_check.rs (native.rs)
      {mod, air, trace, interaction, native}.rs
  proof/                        # orchestration — SPLIT <- proof.rs (6.4k, 95% tests)
    {mod, claim, balances, prove, verify}.rs
    tests/                      # relocated #[cfg(test)] blocks
  reference/
    ecdsa.rs                    # <- ecdsa.rs (native ECDSA; kept iff test-reachable)
  debug/                        # <- debug/ (kept iff test-reachable)
```

Every `components/*` module uses the same internal split already proven in `scalar_mod_mul/`:
`air.rs` (constraints / `evaluate`), `trace.rs` (base-trace + lookup-data generation), `interaction.rs`
(logup interaction trace), plus `relation.rs` / `layout.rs` where the component owns relations or a
nontrivial column layout.

## 5. Old → new mapping

| Current | New | Note |
|---|---|---|
| `lib.rs` | `lib.rs` | module decls + re-exports updated |
| `types.rs`, `constants.rs` | same (root) | foundational, shared |
| `limbs.rs`, `field_ops.rs` | `field/limbs.rs`, `field/ops.rs` | |
| `fp_solinas.rs`, `fp_solinas_air.rs` | `field/solinas/native.rs`, `field/solinas/air.rs` | |
| `curve.rs`, `projective.rs` | `curve/affine.rs`, `curve/projective.rs` | native EC |
| `range_checks/*` | `range_checks/*` | verbatim |
| `scalar/canonical_lt.rs` | `gadgets/canonical_lt.rs` | shared gadget |
| `projective_air.rs` | `components/projective_rcb_mul/{air,trace,interaction,relation}.rs` | **split** |
| `public_key_curve_air.rs`, `public_key_check.rs` | `components/public_key_curve/{air,trace,interaction,native}.rs` | |
| `setup_air.rs`, `setup_witness.rs`, `cert_bind.rs` | `components/scalar_setup/{air,trace,witness,cert_bind}.rs` | |
| `scalar/scalar_mod_mul/*` | `components/scalar_mod_mul/*` | verbatim |
| `public_inputs.rs` | `components/public_inputs/{air,trace,relation}.rs` | |
| `fake_glv_scalar.rs` (+WIP), `fake_glv_decompose.rs` | `components/fake_glv/scalar/{air,trace,decompose}.rs` | |
| `fake_glv_selector.rs`, signed/direct/lsb operands | `components/fake_glv/selector/*` | live operands only |
| `fake_glv_chain*.rs` | `components/fake_glv/chain/{native,continuity,expansion,schedule}.rs` | |
| `fake_glv_ec_source.rs`, `fake_glv_prepared_point_source.rs` | `components/fake_glv/ec_source/*` | live provider only |
| `prepared_table.rs`, `prepared_point.rs` | `components/fake_glv/prepared_table/{air,trace,interaction,point}.rs` | **split** |
| `final_add_air.rs` | `components/final_add/{air,trace,interaction}.rs` | |
| `final_check_air.rs`, `final_check.rs` | `components/final_check/{air,trace,interaction,native}.rs` | |
| `proof.rs` | `proof/{mod,claim,balances,prove,verify}.rs` + `proof/tests/` | **split** |
| `ecdsa.rs` | `reference/ecdsa.rs` | iff test-reachable, else delete |

## 6. Deletion policy & determining the live set

**Definition of LIVE:** an item is live iff reachable (transitively) from `prove_current_air_monolithic`,
`verify_current_air_monolithic`, or `relation_balances()`, or it is a test (and its support code) that
exercises those entry points.

**Determining it (first phase of implementation):** build the reachability set from the monolithic
entry points + the `Components` struct they instantiate + `relation_balances()`. Anything not in the
closure, and not test-support for it, is a deletion candidate.

**Expected deletions (to be confirmed by the reachability pass):**
- Dormant relations/lookups not in `relation_balances()` — `Selector4x4`, `Selector16Decode`,
  `FinalSelector` and the `fake_glv_selector_lookup.rs` provider/consumer scaffolding.
- Standalone `prove_*_slice` / `*_proof_slice` provers used only by slice tests.
- The `from_inputs_with_arbitrary_fake_glv_hints` constructor path and the `#[ignore]`'d e2e/diagnostic
  tests, plus helpers reachable only from them.
- Compile-time-disabled constraint code: `SCALAR_MOD_MUL_ENABLE_AB_*` (=false), `*_UNUSED_*`, and the
  branches they gate.

**Items flagged AMBIGUOUS** (resolve in the plan, never delete on a guess): the fake-GLV operand
providers (signed/direct/lsb), `fake_glv_prepared_point_source.rs`, `reference/ecdsa.rs`, `debug/`.
The safety net for every deletion is: it must still `cargo build --all-targets` and pass the full test
suite afterwards; if a deletion breaks either, it was live and is reverted.

## 7. Behavior-preservation & verification strategy

A pure module move is behavior-preserving by construction (Rust item relocation + `use`/`mod` fixes do
not change semantics). We *prove* it rather than assert it:

1. `git tag pre-reorg-2026-06-08` on current HEAD (recovery point for all deleted dormant code).
2. **Golden baseline:** capture a deterministic serialized-proof hash (and the `relation_balances`
   vector) from the live end-to-end prove/verify test before any change.
3. **Incremental, always-compiling steps.** After every step: `cargo build --all-targets` + full
   `cargo test` (rtk) must be green.
4. **Final gate (authoritative):** full test suite green, the `relation_balances` vector identical to
   baseline, and the verifier-bound `claim` (public inputs, `log_sizes`, claimed_sums) identical to
   baseline. **Corroborating:** the e2e serialized-proof hash == baseline (stwo proving is
   channel-deterministic, so this should hold; if the backend turns out non-deterministic, the
   relation_balances + claim equality is the binding check). Any divergence in the authoritative checks
   means a non-pure change slipped in — stop and fix.

## 8. Migration order (phases)

1. **Tag + baseline** (§7.1–7.2).
2. **Reachability pass** — produce the concrete LIVE/DEAD/AMBIGUOUS inventory (§6).
3. **Dead-code elimination** — delete confirmed-dead items; build + test green. (Done before moving, so
   less code is relocated.)
4. **Foundational layers** — move `field/`, `curve/`, `gadgets/`, `range_checks/`; fix imports; build+test.
5. **Components, one subsystem at a time** — `projective_rcb_mul` (split), then the rest; the two
   monoliths (`projective_rcb_mul`, `fake_glv/prepared_table`) are split during their move. Build+test
   after each subsystem.
6. **proof/ split** — separate orchestration from its 6k test lines; build+test.
7. **Final gate** (§7.4) + update `lib.rs` re-exports + doc-comment paths.

Each phase is independently committable, keeping the branch green throughout.

## 9. Risks & mitigations

| Risk | Mitigation |
|---|---|
| A "pure move" accidentally reorders an AIR emission → silent wrong proof | Golden proof-hash diff + relation-tracker at the final gate; move whole functions intact, never re-author |
| Deleting something actually live | Reachability pass first; build+tests as net; everything recoverable via the `pre-reorg` tag |
| Losing in-progress general-path work | Preserved in git history (tag + existing commits); WIP `fake_glv_scalar.rs` carried into `fake_glv/scalar/` |
| Large import churn introduces compile errors | Incremental per-subsystem moves, compile after each |
| `mix_into` / registration order drift during proof.rs split | Keep the exact call order; final-gate proof hash catches any drift |

## 10. Acceptance criteria

- New tree matches §4; no production file > ~800 lines without a structural reason.
- `cargo build --all-targets` and `cargo test` green.
- E2E proof hash and `relation_balances` identical to the pre-reorg baseline.
- No dead/dormant production code remains in the live tree (the `pre-reorg` tag holds the recoverable copy).
- Public `prove`/`verify` entry points remain callable at stable paths (via `lib.rs` re-exports).
