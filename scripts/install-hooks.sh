#!/usr/bin/env bash
#
# One-time setup: point git at the version-controlled hooks in .githooks/ so
# the pre-commit lint gate runs before every commit.
#
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
git config core.hooksPath .githooks

echo "pre-commit hook enabled (core.hooksPath -> .githooks)"
echo "bypass it for a single commit with: git commit --no-verify"
