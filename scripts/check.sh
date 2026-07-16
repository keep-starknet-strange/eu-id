#!/usr/bin/env bash
#
# Local lint gate: clippy (warnings = errors) + rustfmt check.
#
# This is the single definition of "lint" for the workspace. `make check` and
# the pre-commit hook both delegate here, and CI runs `make check`, so local
# and CI lint results cannot diverge.
#
set -euo pipefail

# Run from the repository root regardless of the caller's working directory.
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

echo "==> cargo clippy (warnings treated as errors)"
# Deferred clippy *style* lints, allowed workspace-wide to keep the gate green
# while the crypto crates are actively developed. These are non-correctness lints
# (arg counts, index loops, elidable lifetimes, etc.); revisit in a cleanup pass.
cargo clippy -- -D warnings \
    -A clippy::too_many_arguments \
    -A clippy::needless_range_loop \
    -A clippy::needless_borrow \
    -A clippy::needless_lifetimes \
    -A clippy::redundant_closure \
    -A clippy::explicit_auto_deref \
    -A clippy::manual_memcpy \
    -A clippy::manual_is_multiple_of \
    -A clippy::missing_safety_doc \
    -A clippy::doc_lazy_continuation

echo "==> cargo fmt --check"
cargo fmt -- --check

echo "==> lint passed"
