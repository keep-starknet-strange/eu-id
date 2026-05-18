# eu-id

STARK-based zero-knowledge proofs for the EU Digital Identity Wallet — a
proof-of-concept that proves *"I am over 18"* from a digitally signed identity
credential without revealing the holder's date of birth.

> **Status — research prototype.** Built to contribute a missing technical
> perspective to a public EU standards discussion; it is **not** a production
> library. The code has **not been audited** and must not be used in
> production. This iteration produces *succinct* proofs (small and fast to
> verify) but **not yet zero-knowledge** proofs — witness-hiding is a planned,
> well-understood follow-up, disclosed honestly here and in the project
> writeup.

## What this is

The EU Digital Identity Wallet needs privacy-preserving selective disclosure.
The Commission's "Topic G" analysis weighs BBS+ signatures and zk-SNARKs but
omits STARKs entirely. `eu-id` is the smallest credible artifact showing STARKs
belong in that comparison: an in-circuit pipeline — SHA-256 hashing, ECDSA
P-256 signature verification, and ISO mdoc credential parsing — that proves an
age predicate over a real ISO/IEC 18013-5 credential.

See [`docs/SPEC.md`](docs/SPEC.md) for the architecture and
[`docs/ROADMAP.md`](docs/ROADMAP.md) for the development plan.

## Requirements

- **Rust nightly**, pinned by [`rust-toolchain.toml`](rust-toolchain.toml) to
  `nightly-2025-07-14`. `rustup` installs it — together with the `rustfmt` and
  `clippy` components — automatically on first use inside the repository.
- **CPU:** the Stwo SIMD backend prefers x86-64 with AVX2; other targets fall
  back to a scalar backend.

## Getting started

```bash
make build                 # compile the whole workspace
make test                  # run the workspace test suite
./scripts/install-hooks.sh # enable the pre-commit lint gate (one-time)
```

The [`Makefile`](Makefile) is the shared entry point for every common task:

| Command            | Description                                        |
| ------------------ | -------------------------------------------------- |
| `make build`       | compile the whole workspace                        |
| `make test`        | run the workspace test suite                       |
| `make check`       | clippy + rustfmt — the CI lint gate                |
| `make fmt`         | apply rustfmt across the workspace                 |
| `make dev`         | watch sources and re-run `cargo check`             |
| `make bench`       | laptop criterion benchmark suite                   |

Run `make help` for the full list.

## Contributor workflow

Style and lint are enforced consistently across the workspace:

- **Formatting** — [`rustfmt.toml`](rustfmt.toml) defines the workspace format.
  Run `make fmt` (or `cargo fmt`) before committing.
- **Linting** — clippy is configured workspace-wide in the root
  [`Cargo.toml`](Cargo.toml) under `[workspace.lints]`; every crate inherits it
  via `[lints] workspace = true`.
- **Lint gate** — `make check` runs [`scripts/check.sh`](scripts/check.sh):
  clippy with warnings treated as errors, plus a rustfmt check. CI runs the
  exact same `make check`, so a green local check means a green CI lint.
- **Pre-commit hook** — `./scripts/install-hooks.sh` points
  `git config core.hooksPath` at the version-controlled
  [`.githooks/`](.githooks) directory, so the lint gate runs automatically
  before each commit. Bypass it for a single commit with
  `git commit --no-verify`.

## Project layout

```
crates/
  stwo-p256/     ECDSA P-256 verification AIR + native reference
  stwo-sha256/   SHA-256 AIR (M31 lookup-table design)
docs/            specification, roadmap, and design notes
scripts/         developer tooling
.githooks/       version-controlled git hooks
```

Further component crates — mdoc parsing and the integration "Big AIR" — and the
demo CLI land as the roadmap progresses.

## License

To be determined before public release.
