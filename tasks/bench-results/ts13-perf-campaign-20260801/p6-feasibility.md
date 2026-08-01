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

## Live geometry census

The final release shape dump reports 16,890,800 AIR-reference cells through
interaction and 65,536 post-interaction cells:

- preprocessed: 1,187,600 cells;
- trace: 11,965,152 cells;
- interaction: 3,738,048 cells;
- post-interaction: 65,536 cells.

The preprocessed count includes 401 AIR references. Tree 0 deduplicates these
references by column ID before commitment. It commits 319 unique columns and
953,584 cells. Therefore, the physical commitment total through tree 3 is
16,722,320 cells, not 16,956,336 cells. The table below ranks AIR-reference
mass because shared preprocessed columns cannot be assigned to one consumer.

| Module | Preprocessed | Trace | Interaction | Reference total | Share |
| --- | ---: | ---: | ---: | ---: | ---: |
| Keccak service | 211,104 | 8,121,376 | 704,640 | 9,037,120 | 53.50% |
| Device ML-DSA | 461,472 | 1,580,256 | 1,641,152 | 3,682,880 | 21.80% |
| MSO SHA-256 | 40,976 | 1,065,472 | 131,648 | 1,238,096 | 7.33% |
| Issuer ML-DSA | 151,888 | 212,016 | 352,896 | 716,800 | 4.24% |
| Revocation ML-DSA | 143,760 | 207,952 | 320,384 | 672,096 | 3.98% |
| Device ExpandA | 88,064 | 197,632 | 200,704 | 486,400 | 2.88% |
| Other 14 modules | 90,336 | 580,448 | 386,624 | 1,057,408 | 6.26% |

The Keccak post-interaction argument adds eight log-13 columns, or 65,536
physical cells. The Keccak service and device ML-DSA module contain 75.30% of
all AIR-reference cells through interaction. The first three modules contain
82.7% after assigning the post-interaction cells to Keccak.

The preprocessed-column audit found no unused active column. Tree 0 already
shares identical IDs and saves 234,016 cells. The only small unimplemented
sharing candidate is the static SampleInBall schedule. It can save at most
57,344 physical cells, or about 0.34% of the circuit. It cannot affect the
phone decision.

This mass is not removable cleanup. A geometry path must redesign the Keccak
carrier, private-device inverse NTT, and private SHA arithmetizations while
preserving every relation and proof check. Reducing parser, binding, or public
modules cannot close the phone gap.

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

## Backend feasibility bound

A proof-identical rewrite of the pinned STWO backend cannot meet the phone
gate. Pixel 8 needs a 4.33x speedup inside the complete AIR core. Galaxy A54
needs a 4.14x AIR-core speedup. If all commitments, GKR, and STARK proving took
zero time, the remaining SDK work would still take 2,302 ms on Pixel 8 and
2,114 ms on Galaxy A54.

An optimistic model applies all of these gains at once:

- 3x for composition generation;
- 3x for all pre-STARK commitments;
- 2x for the already optimized GKR path;
- 2x for all other STARK work;
- 2x for interaction generation.

That model gives only a 1.79x Pixel 8 speedup and a 1.90x Galaxy A54 speedup.
The pinned backend already uses NEON field arithmetic, packed-field inlining,
parallel Blake2s, and parallel GKR, sumcheck, and MLE work. The only unused
measured descendant removes about 4.5% of GKR and less than 1% of total prove
time. Therefore, backend-only work is useful for incremental improvement but
is not a path to the 2,000 ms gate.

A backend rewrite would also need a fixed full-proof byte-parity test before
the first change. The current tests cover field and GKR parity but do not pin
every serialized TS13 proof byte.

## AIR redesign bound

Geometry reduction can meet the arithmetic bound only through a full redesign
of the largest modules. Under the unrealistically favorable assumption that
time scales linearly with AIR-reference cells, Pixel 8 needs at most 6,198,459
cells and Galaxy A54 needs at most 5,771,673 cells.

If every module except Keccak and device ML-DSA remains unchanged, those two
modules must shrink by 84.06% on Pixel 8 and 87.41% on Galaxy A54. Deleting the
complete 7,454,720-cell Keccak carrier and the complete 2,490,368-cell inverse
NTT butterfly would still miss the optimistic geometry target. Neither family
can actually be deleted. This proves that ordinary column cleanup is too
small.

The only arithmetically credible staged budget found by the audit is:

| Replacement or retained work | Maximum cells |
| --- | ---: |
| Complete Keccak argument | 1,000,000 |
| Batched private inverse-NTT and mod-q argument | 350,000 |
| Byte-oriented private SHA-256 AIR | 200,000 |
| Retained circuit work | 4,125,000 |
| Total | 5,675,000 |

This is about a 2.99x reduction from the AIR-reference geometry. It requires a
complete Keccak round argument tied to every sponge boundary, a batched
inverse-NTT argument tied to every ExpandA cell and canonical residue check,
and a byte-oriented SHA-256 AIR that keeps padding, digest, and field relations
inside the proof.

The Keccak replacement must be the first isolated prototype. Stop this path if
the prototype exceeds 1.5 million cells or 1.2 seconds of complete Keccak and
auxiliary proof time on Galaxy A54. A smaller trace can still lose if its new
argument costs more than the removed trace and GKR.

Every accepted prototype must keep the theorem, all ML-DSA-65 roles, current
PCS security, local proving, public-input unlinkability, and all source
tie-backs. It must pass reference vectors, forged carry and residue tests,
disconnected-multiset tests, boundary mutations, artifact regeneration, the
A1/A2/B unlinkability test, and the complete release matrix before Firebase.

## Scope boundary

The 2,000 ms gate remains unmet. A credible next attempt requires the AIR
redesign above. A proof-identical pinned-STWO rewrite cannot close the measured
gap. The remaining scope choices are:

- authorize the staged AIR redesign and its new proof arguments;
- accept incremental backend work without claiming that it can meet 2,000 ms;
- change the phone target or use non-local proving.

The last option changes the product trust or deployment model. Weakening PCS
security, dropping a required proof check, changing ML-DSA-65 roles, or reusing
a credential proof is not acceptable.
