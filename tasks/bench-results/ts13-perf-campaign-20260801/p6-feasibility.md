# P6 feasibility result

Date: 2026-08-01

Status: complete. P6 has no implementation in the fixed campaign scope. The
final phone data proves that witness parallelism cannot meet the 2,000 ms
prove target.

Privacy claim: `public-input unlinkable; transcript zero knowledge pending`

## Final evidence

- Final circuit hash:
  `2eff9e073151b4bce733516f4b6dd411b6d48ef5425fd93d41c64bedf524fea9`
- Firebase matrix: `matrix-92u1aei93c81a`
- Numeric matrix ID: `4904946063125125660`
- Firebase history: `bh.f5f036aa81c4230a`
- API: `proveIdentity`
- Runtime: six workers, 2 MiB proof-thread stack, 16 MiB worker stacks

Each phone log contains one summary and 25 ordered phase records. The phase
records are hierarchical. The STWO phase records are inside the STARK total,
and the AIR and SDK totals contain the earlier phase records. The analysis
does not add nested records together.

## Measured limit

Times are milliseconds. The residual deletes witness generation, Tree 2
interaction generation, and the complete post-interaction GKR phase. This is
an impossible best case, not an optimization projection.

| Device | Prove | Cut needed | Total speedup needed | Witness | Tree 2 write | GKR | Residual after all three are free |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Pixel 8 | 5,450 | 3,450 (63.30%) | 2.725x | 933.999 | 1,157.870 | 786.518 | 2,571.613 |
| Galaxy S24 Ultra | 2,755 | 755 (27.40%) | 1.378x | 313.930 | 731.030 | 395.741 | 1,314.299 |
| Galaxy A54 | 5,853 | 3,853 (65.83%) | 2.927x | 687.940 | 1,195.288 | 1,023.495 | 2,946.277 |

The impossible residual is still 571.613 ms above the gate on Pixel 8 and
946.277 ms above the gate on Galaxy A54. Therefore, complete removal of P6
witness work cannot meet the target on the two binding phones.

The other dominant phases are also structural:

| Phase | Pixel 8 | Galaxy S24 Ultra | Galaxy A54 |
| --- | ---: | ---: | ---: |
| Tree 1 commit | 481.873 | 309.932 | 694.408 |
| Tree 2 commit | 220.230 | 103.707 | 264.563 |
| STARK prove total | 1,515.155 | 679.530 | 1,636.499 |

On Pixel 8 and Galaxy A54, the required cut is almost equal to the complete
Tree 2 write, GKR, and STARK time combined. A solution must remove almost all
three phases. Any remaining time must be offset by witness or commitment work.
Runtime tuning, serialization, and more witness threads cannot do this.

## Final P6 decision

Do not add more witness-generation parallelism.

- The canonical witness path already runs independent ML-DSA role work in
  parallel.
- Keccak witness construction and SHA trace work already use parallel paths.
- Serialization is 2.306 ms or less and is not material.
- Even zero-cost witness generation cannot close the Pixel 8 or Galaxy A54
  gap after zero-cost Tree 2 generation and GKR.

This decision preserves the theorem, all ML-DSA-65 roles, transcript order,
PCS security, local proving, and public-input unlinkability.

## Existing-work audit

The audit covered 66 local branches and 34 registered worktrees. It found no
unmerged compatible candidate with a material Android gain.

- All five accepted P5 Keccak changes are already in the canonical branch.
- The measured claimed-sum parallelism gain is already present.
- Fat LTO and one code-generation unit are already active.
- The final SDK already uses the Firebase-selected fixed worker pool.
- The affinity experiment failed its fixed A/B/B/A rule.
- The allocator experiment produced no valid Android candidate.
- The remaining commitment-overlap experiment can save at most the complete
  59 to 88 ms Tree 0 commit. It increases live memory, targets an obsolete
  STWO API, and has no benchmark evidence.
- Other SHA-channel branches change transcript semantics and are outside the
  fixed scope.

## Scope boundary

The 2,000 ms gate remains unmet. A credible next attempt requires at least one
material scope expansion:

- redesign the AIR to reduce trace and interaction geometry;
- change or optimize the pinned STWO prover backend; or
- change the phone target or use non-local proving.

The last option changes the product trust or deployment model. Weakening PCS
security, dropping a required proof check, changing ML-DSA-65 roles, or reusing
a credential proof is not acceptable.
