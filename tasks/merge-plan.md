# Merge & Cleanup Plan — coprocessor + mdoc into `feat/proof-reductions`

Goal state: `feat/proof-reductions` contains all completed work (mdoc v1 +
perf, nonce monolith wiring, the ECDSA coprocessor crate feature-gated
default-OFF); the main checkout's worktree is **clean**; stale worktrees are
pruned; **GKR work stays on its own branch, unmerged** (Lucas's call). No
pushes — leave that to Lucas. Never enable the `ec-coprocessor` feature by
default; never delete `crates/stwo-p256` (that is BL6, gated on the soundness
campaign — out of scope here).

**House rules:** run every listed gate before its commit; never weaken a test;
`rtk` prefix on commands; commit messages as given (no Co-Authored-By lines);
on ANY listed STOP condition, write what you found to
`tasks/mdoc-mailbox/questions/` (next Q number) and end with a report instead
of improvising. Grouped commits, not one blob.

## Inventory (verified 2026-07-04 — re-verify at start, it moves)
| checkout | branch | role |
|---|---|---|
| `/Users/lucas/eu-id` | `feat/proof-reductions` (ahead 57, ~84 modified + untracked) | main; target of all merges |
| `.claude/worktrees/s4-lite` | `s4-lite` | ECDSA coprocessor (crate `eu-id-ec-coprocessor`) |
| `.claude/worktrees/mdoc-full-plan` | `codex/full-mdoc-plan` | Codex worker executing tasks/mdoc-full-impl-plan.md |
| `.claude/worktrees/a1-typed-mults` | `perf/a1-typed-multiplicities` | A-queue perf work |
| (tmp scratchpad) `wo30-redo` | `wo30-128bit` | WO-3.0 re-split work |
| `.claude/worktrees/agent-ac5b003fdc56fee83` | `worktree-agent-…` | ephemeral agent leftover |

## Phase M0 — fresh inventory + freeze notice
1. `git worktree list`; `git branch -a`; `rtk git status` in the main checkout
   AND in each worktree. Record everything in your report before touching
   anything.
2. Write `tasks/parity/mailbox/answers/NOTICE-merge-freeze.md` (frontmatter
   `type: notice`, from: merge agent, date): "main tree entering merge window;
   worker sessions: reach a committed quiet point and pause until this notice
   is deleted." Commit it (`git add -f`).

## Phase M1 — bring the MAIN checkout to quiet (grouped commits)
Gates FIRST, once, before any commit:
```
rtk cargo build --workspace
rtk proxy cargo test -p eu-id-prover --test mdoc_support
rtk proxy cargo test -p eu-id-prover --test nonce_signature
rtk proxy cargo test -p eu-id-prover --test identity_api
rtk proxy cargo test -p eu-id-prover --lib
rtk proxy cargo test -p eu-id-prover --test nonce_signature --release -- --include-ignored   (slow gate 1)
rtk proxy cargo test -p eu-id-prover --test mdoc_support isolated_mdoc_circuit_profile_proves_and_verifies --release -- --ignored   (slow gate 2)
rtk cargo clippy -p eu-id-prover -p eu-id-ffi ; rtk proxy cargo fmt --check
```
All green ⇒ commit in this order (use `git add -f` for anything under `tasks/`):
1. `feat(mdoc): isolated mdoc v1 profile circuit + host parser` — untracked
   `crates/eu-id-prover/src/mdoc.rs`, `tests/mdoc_support.rs` changes,
   `docs/mdoc-credential-format.md`, related `docs/credential-format.md` edit.
2. `feat(prover): fold nonce P-256 into the identity monolith` — `src/nonce.rs`
   (untracked), `src/lib.rs`, `src/fixtures.rs`, `src/shape_dump.rs`,
   `src/bin/eu-id.rs`, `tests/{nonce_signature,identity_api,e2e_soundness,compose_p256_sha}.rs`,
   `benches/common/stages.rs`, `benches/identity_bench.rs`,
   `examples/{bench_report,fri_sweep}.rs`, `crates/eu-id-ffi/src/lib.rs`,
   `crates/sdk/src/{lib,mapping}.rs`.
3. `perf(mdoc): phase 0/0b — mdoc bench, shape dump, dedup invariant guard` —
   `benches/mdoc_bench.rs` (untracked), `crates/air-core/src/lib.rs` guard,
   perf-log rows, mdoc.rs comment-only lines if not already in (1).
4. `docs(tasks): mdoc + merge planning specs` — `git add -f
   tasks/mdoc-credential-format-spec.md tasks/mdoc-full-impl-plan.md
   tasks/mdoc-real-credentials-spec.md tasks/merge-plan.md tasks/todo.md
   tasks/mdoc-mailbox/`.
5. Remainder sweep: whatever `rtk git status` still shows modified (the WO
   perf-queue stragglers in stwo-p256/stwo-sha256/predicates/Cargo.*):
   `perf(parity): pre-merge sweep of uncommitted WO-queue work` with the full
   file list in the commit body. EXCEPTION: if any remaining change is
   exclusively GKR-v2 material (stwo-fork patches, files only used under the
   `gkr-spike` feature that are NOT part of the committed Q-024 freeze state):
   move those to a new branch `spike/gkr-v2` (branch from HEAD, commit there,
   `git checkout feat/proof-reductions -- <files>` to restore), do NOT merge
   it. Already-committed feature-gated gkr code stays where it is (frozen per
   Q-024).
STOP condition: any gate red ⇒ no commits, mailbox with the failure verbatim.

## Phase M2 — merge `codex/full-mdoc-plan`
Precondition: its worktree `git status` is CLEAN (worker at quiet). If dirty ⇒
skip, record, continue.
1. `git merge --no-ff codex/full-mdoc-plan -m "merge: mdoc full-impl-plan work (codex worker)"`.
2. Conflict rule: `tasks/**` docs → resolve by keeping BOTH sides' content
   (union; these are logs/specs). Code conflicts in `crates/**` ⇒ STOP +
   mailbox (do not hand-resolve prover code).
3. Re-run the full M1 gate list. Red ⇒ `git merge --abort`… (already
   committed; instead) ⇒ STOP + mailbox with the failing test names.

## Phase M3 — merge `s4-lite` (the coprocessor), feature-gated
Precondition: s4-lite worktree CLEAN. If dirty ⇒ skip, record (the freeze
notice asks them to quiesce; a second run of this plan picks it up).
1. `git merge --no-ff s4-lite -m "merge: eu-id-ec-coprocessor v1 (feature-gated, default off)"`.
2. Post-merge assertions (all MUST hold):
   - `grep -rn "ec-coprocessor" **/Cargo.toml` shows the feature NOT in any
     `default = [...]` list;
   - `rtk cargo build --workspace` (default features) green;
   - full M1 gate list green (default path byte-identical in behavior);
   - feature-on check: `rtk cargo test -p eu-id-ec-coprocessor` (its own
     suite) green;
   - `crates/stwo-p256` untouched by the merge except workspace-member lists.
3. Conflict rule: same as M2 (tasks/** union; crates/** code conflict outside
   Cargo.toml/Cargo.lock membership lines ⇒ STOP + mailbox).

## Phase M4 — park GKR, prune stale worktrees
1. GKR: confirm branch `spike/gkr-v2` (from M1.5) or, if the GKR-v2 arc lives
   in a worktree/branch you found in M0, ensure it is COMMITTED on its own
   branch. Do not merge it anywhere. Record the branch name + tip SHA in the
   report and in `tasks/parity/STATUS.md` ("GKR-v2 parked: <branch>@<sha>,
   reopener gate = Q-026").
2. For each remaining worktree: if its branch is fully merged (M2/M3) and its
   status is clean ⇒ `git worktree remove <path>` and keep the branch. If it
   has uncommitted changes or commits from the last 24 h that are NOT merged ⇒
   leave it, record it as active. Never remove `wo30-redo` or any worktree
   with a dirty status.
3. Delete `tasks/parity/mailbox/answers/NOTICE-merge-freeze.md` (commit).

## Phase M5 — final verification + report
1. `rtk git status` on the main checkout: MUST be clean (nothing modified,
   nothing untracked outside ignored dirs).
2. Full M1 gate list one last time on the merged tree, PLUS:
   `RAYON_NUM_THREADS=1 cargo bench -p eu-id-prover --bench mdoc_bench`
   recorded to perf-log (post-merge row) — confirm mdoc prove still ≤ 2.0× the
   POC monolith.
3. Append a dated merge summary to `tasks/parity/STATUS.md`: branches merged
   (with SHAs), branches parked, worktrees pruned/left, gate results.
4. Do NOT push. Report: the M0 inventory, every commit made (hash + message),
   merges done/skipped and why, final status output, and any mailbox files you
   filed.
