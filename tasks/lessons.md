# Repository rules

## Evidence

- Trace the exact prover entrypoint before you name a proof or benchmark.
- Trace the exact verifier entrypoint.
- Trace the fixture constructor.
- Count composed job geometry after all size-dependent credential fields change.
- Inspect every statement field.
- Do not infer behavior from a function or benchmark name.
- Treat comments and campaign prose as hypotheses.
- Use executable constraints and verifier behavior as evidence.
- Check public serialization.
- Check relation signs and multiplicities.
- Search hidden files with `rg --files -uu` or `git ls-tree -r HEAD`.
- Search the root working tree before saying that an ignored task file is absent.
- Do not report a required file as absent before this search.
- Confirm that each filtered test executes at least one test.
- A result with `0 passed` is not test evidence.

## Proof tests

- Run a live composed proof for each PCS domain class before you report its frontier row.
- Do not infer prover support from interpolation and envelope formulas.
- Name both the source commit and artifact commit for each PCS frontier row.
- Do not use a parameter-only commit with an uncommitted generated artifact as evidence.
- Run all proof tests with `--release`.
- Use a release profile with debug information when you need symbols.
- Do not use a debug proof as final evidence.
- Set `RAYON_NUM_THREADS` explicitly.
- Record the effective Rayon thread count in each result.
- Record effective thread stacks; an explicit builder stack overrides
  `RUST_MIN_STACK`.
- On the 12-core demo host, set `RAYON_NUM_THREADS=12`.
- Run one memory-heavy test harness thread with `--test-threads=1`.
- Do not confuse the harness thread count with the Rayon worker count.
- Prove the complete control fixture before each mutation test.
- Build an optional witness arm before you test malformed forms of that arm.

## Trust boundaries

- Keep required issuer verification inside the STARK.
- Keep required device verification inside the STARK.
- Keep required revocation verification inside the STARK.
- Do not replace a required AIR check with native verification.
- Pin the tree-zero root with verifier-trusted data.
- Do not trust a tree-zero root from the proof or envelope.
- Fail closed when the verifier cannot obtain the trusted root.
- Hold every public preprocessing input fixed during a privacy comparison.
- Test an intentional public-key change in a separate allowlist test.

## Derived values

- Constrain each security-relevant derived value to its canonical source.
- Transcript mixing proves agreement only.
- Transcript mixing does not prove derivation.
- Constrain ML-DSA `tr` to `SHAKE256(pkEncode(rho, t1), 64)`.
- State each accepted public canonicalization boundary.
- Add a forged derived witness to each boundary regression.
- Require the AIR to reject the forged witness.
- Preserve the normative transcript mix order.
- Bind a derived value in the AIR that consumes the value.

## AIR soundness

- Derive the OODS degree from the verifier's recombined composition polynomial.
- Do not use one split-part degree as the whole OODS bound.
- Audit each state column directly.
- Audit each transition directly.
- Audit each permutation tuple field directly.
- Audit each relation multiplicity directly.
- Do not use honest vectors as the only soundness evidence.
- Do not use witness mutations as the only soundness evidence.
- Check each lookup gate for a zero-value bypass.
- Check each memory tuple for an omitted field.
- Isolate the domain tag in a cross-domain lookup test.
- Balance the forged multiset when the test removes the tag.
- Require rejection when the test restores the tag.
- Give opposite-sign lookup roles distinct tuple tags when identical tuples could cancel.
- Copy attack state into immutable relation state before Rayon evaluation.
- Use the same attack state for shape inference, proving, and verification.

## Public preprocessing

- Distinguish AIR self-containment from end-to-end soundness.
- Randomized or out-of-domain checks do not detect fixed-versus-fixed tautologies.
- Derive a fixed column when the verifier can reconstruct it from other fixed columns.
- Read each aliased preprocessed representative once and clone its field value for logical uses.
- Identify each value that the verifier computes outside the AIR.
- State the trust boundary for each computed value.
- Do not describe verifier preprocessing as an AIR constraint.
- If all arithmetic must be in the STARK, reject native GKR acceptance.
- Constrain the GKR result in the outer AIR.

## Mobile benchmarks

- Do not run a latency sample while another build, proof, or benchmark uses the host.
- Run final desktop performance samples in one serial campaign.
- Identify the measured function before you reuse a mobile harness.
- Benchmark only the canonical `proveIdentity` path.
- Use the same APK for each physical-device comparison.
- Put all binding phones in one Firebase matrix with the same APK pair and
  environment.
- Keep each Android benchmark log record below 3,000 UTF-8 bytes.
- Measure the final source revision.
- Use counter-ordered A/B runs for an optimization comparison.
- Select performance-core CPU identifiers explicitly.
- Exclude the lowest-capacity CPU cluster.
- Record selected and excluded CPU identifiers.
- Record the topology source.
- Use all-core scheduling only when the user requests it.
- Stop performance work when the user defers performance.
- Do not add an optimization after that instruction.
- Resume a deferred benchmark only after the user explicitly reauthorizes it.
- Prove and verify a regenerated mobile fixture locally before uploading it.
- Regenerate the signed credential fixture when the canonical mdoc profile changes.

## Artifact provenance

- Record the exact source commit for each artifact.
- Build each benchmark executable in a fresh target directory, record its hash,
  and run one proof before the timing campaign.
- Record the fixture SHA-256.
- Record each binary, AAR, and APK SHA-256.
- Record the circuit hash.
- Record the shape-manifest digest.
- Record the soundness source-tree digest.
- Record `Cargo.lock`, the Rust toolchain, and enabled features.
- Use complete source roots for the soundness digest.
- Use a closed allowlist for recursive generated-file exclusions.
- Regenerate the artifact after each soundness-source change.
- Reject artifact drift in verification.
- Remove artifact relation-use records when their AIR components are deleted.
- Mark a retained transcript-only relation as reserved instead of inventing uses.
- Do not change transcript or domain-separator bytes during a terminology cleanup.
- Remove generated Android build directories before hashing the source tree.
- Freeze and record an exact checkpoint before parallel campaign edits begin.
- Reuse one isolated Cargo target for a serial package frontier.
- Copy each package out before you switch to the next source checkpoint.
- After a geometry change, validate a live proof against the artifact input.
  Static artifact generation alone does not prove that the input is current.
- Bind every GKR input vector before its randomized compression challenges.
  Transcript messages do not create a missing global input oracle.
- Compare complete relation denominators before you cancel lookup numerators.
  Equal-looking coefficients do not cancel across different tuples.

## Scope

- Re-read every new final mailbox answer before continuing dependent work.
- Treat a final mailbox policy as superseding earlier measurements and checkpoints.
- Apply a user scope change immediately.
- Treat a checkpoint result as incomplete when the user authorizes the full campaign.
- Stop cloud and device work when the user limits a benchmark to the computer.
- Resume cloud or device work when the user explicitly authorizes it again.
- Treat a direct statement that Firebase is approved as authorization for the
  scoped Firebase uploads and test runs. Do not ask for the same approval again.
- Treat a direct authentication confirmation from the user as the mailbox
  confirmation. Run the required non-interactive probe at once. Record the
  mailbox confirmation only after the probe succeeds.
- Put external-state questions in the main-repository mailbox when the user selects that channel.
- Remove excluded work from the active plan.
- Remove compatibility routes when the user selects one canonical API.
- Do not keep a one-variant routing enum.
- Require mandatory trust inputs in the canonical constructor.
- Do not invent a protocol version to select an encoding rule.
- Check the official credential schema before you restrict CBOR map order.
- Keep the core proof contract independent of wallet code.
- End the core contract at the exported prove and verify API.
- Treat the proof bytes as opaque at that boundary.
- Check the repository root for task files even when source work uses a worktree.
