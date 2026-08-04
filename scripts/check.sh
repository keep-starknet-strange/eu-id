#!/usr/bin/env bash
#
# Local lint gate: clippy (warnings = errors) + rustfmt check.
#
# This script defines the workspace lint check.
# `make check`, the pre-commit hook, and CI use this script.
#
set -euo pipefail

# Run from the repository root regardless of the caller's working directory.
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-12}"
export RAYON_NUM_THREADS="${RAYON_NUM_THREADS:-12}"

echo "==> cargo clippy (warnings treated as errors except the declared style allow-list)"
# Permit these Clippy style lints during active cryptographic development.
# These lints do not report correctness defects.
# Review them during a later cleanup.
cargo clippy --locked --release --workspace --all-targets \
    -j "$CARGO_BUILD_JOBS" -- -D warnings \
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
cargo fmt --all -- --check

echo "==> locked dependency graph"
cargo metadata --locked --offline --no-deps --format-version 1 >/dev/null

echo "==> product profile artifact drift"
python3 scripts/product_profile_artifacts.py --check

echo "==> shell syntax"
bash -n scripts/*.sh crates/eu-id-ffi/build-xcframework.sh mobile/build-bench-android.sh

echo "==> lint passed"
