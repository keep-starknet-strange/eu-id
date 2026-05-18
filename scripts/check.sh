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
cargo clippy -- -D warnings

echo "==> cargo fmt --check"
cargo fmt -- --check

echo "==> lint passed"
