#!/usr/bin/env bash
# Run one release command with source-derived, reproducible build settings.
set -euo pipefail

usage() {
    echo "usage: $0 [--allow-dirty] [--print-source-id|--print-packaging-source-id] command [args ...]" >&2
    exit 2
}

allow_dirty=false
print_source_id=false
print_packaging_source_id=false
while [[ "${1:-}" == --* ]]; do
    case "$1" in
        --allow-dirty) allow_dirty=true ;;
        --print-source-id) print_source_id=true ;;
        --print-packaging-source-id) print_packaging_source_id=true ;;
        *) usage ;;
    esac
    shift
done
if $print_source_id && $print_packaging_source_id; then
    usage
fi
if ! $print_source_id && ! $print_packaging_source_id && [[ $# -eq 0 ]]; then
    usage
fi

workspace_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
head_commit="$(git -C "$workspace_root" rev-parse --verify HEAD)"
source_date_epoch="$(git -C "$workspace_root" show -s --format=%ct "$head_commit")"
dirty=false
if [[ -n "$(git -C "$workspace_root" status --porcelain --untracked-files=all)" ]]; then
    dirty=true
fi
if $dirty && ! $allow_dirty; then
    echo "refusing a dirty release build; pass --allow-dirty to label it explicitly" >&2
    exit 1
fi
if [[ -n "${RUSTFLAGS:-}" || -n "${CARGO_ENCODED_RUSTFLAGS:-}" ]]; then
    echo "RUSTFLAGS and CARGO_ENCODED_RUSTFLAGS must be unset" >&2
    exit 1
fi
for profile_override in \
    CARGO_PROFILE_RELEASE_LTO CARGO_PROFILE_RELEASE_CODEGEN_UNITS \
    CARGO_PROFILE_RELEASE_OPT_LEVEL CARGO_PROFILE_RELEASE_DEBUG \
    CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS CARGO_PROFILE_RELEASE_INCREMENTAL \
    CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS CARGO_PROFILE_RELEASE_PANIC \
    CARGO_PROFILE_RELEASE_STRIP; do
    if [[ -n "${!profile_override+x}" ]]; then
        echo "$profile_override must be unset for a canonical release build" >&2
        exit 1
    fi
done
for rust_wrapper in RUSTC_WRAPPER RUSTC_WORKSPACE_WRAPPER; do
    if [[ -n "${!rust_wrapper:-}" ]]; then
        echo "$rust_wrapper must be unset for a canonical release build" >&2
        exit 1
    fi
done

if command -v shasum >/dev/null 2>&1; then
    sha256=(shasum -a 256)
else
    sha256=(sha256sum)
fi
source_sha256="$({
    git -C "$workspace_root" ls-files -c -o --exclude-standard -z -- \
        Cargo.toml Cargo.lock rust-toolchain.toml '.cargo/**' 'artifacts/**' \
        'crates/*/Cargo.toml' 'crates/*/build.rs' 'crates/*/src/**' \
        'crates/*/artifacts/**' 'crates/*/examples/**' 'crates/*/tests/**' \
        'crates/*/benches/**' scripts/reproducible-build.sh \
        scripts/check-reproducible-build.sh \
        | LC_ALL=C sort -z \
        | while IFS= read -r -d '' file; do
            if [[ -f "$workspace_root/$file" ]]; then
                printf '%s\0' "$file"
                "${sha256[@]}" "$workspace_root/$file" | awk '{ print $1 }'
            fi
        done
} | "${sha256[@]}" | awk '{ print $1 }')"
if $print_source_id; then
    echo "$source_sha256"
    exit 0
fi
if $print_packaging_source_id; then
    packaging_source_sha256="$({
        git -C "$workspace_root" ls-files -c -o --exclude-standard -z -- \
            Cargo.toml Cargo.lock rust-toolchain.toml '.cargo/**' 'artifacts/**' \
            'crates/*/Cargo.toml' 'crates/*/build.rs' 'crates/*/src/**' \
            'crates/*/artifacts/**' 'crates/*/examples/**' 'crates/*/tests/**' \
            'crates/*/benches/**' scripts/reproducible-build.sh \
            scripts/check-reproducible-build.sh \
            crates/eu-id-ffi/build-xcframework.sh 'crates/eu-id-ffi/include/**' \
            crates/sdk/uniffi.toml 'crates/sdk/android/**' 'crates/sdk/jvm/**' \
            mobile/build-bench-android.sh 'mobile/EuIdBenchAndroid/**' \
            'mobile/EuIdBench/**' \
            | LC_ALL=C sort -z \
            | while IFS= read -r -d '' file; do
                if [[ -f "$workspace_root/$file" ]]; then
                    printf '%s\0' "$file"
                    "${sha256[@]}" "$workspace_root/$file" | awk '{ print $1 }'
                fi
            done
    } | "${sha256[@]}" | awk '{ print $1 }')"
    echo "$packaging_source_sha256"
    exit 0
fi

export SOURCE_DATE_EPOCH="$source_date_epoch"
export ZERO_AR_DATE=1
export CARGO_INCREMENTAL=0
export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-12}"
export RAYON_NUM_THREADS="${RAYON_NUM_THREADS:-12}"
export LC_ALL=C
export TZ=UTC

echo "release source: commit=$head_commit source=$source_sha256 epoch=$SOURCE_DATE_EPOCH dirty=$dirty" >&2
cd "$workspace_root"
exec "$@"
