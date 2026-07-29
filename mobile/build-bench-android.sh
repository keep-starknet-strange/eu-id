#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORKSPACE_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
ANDROID_SDK_DIR="${EU_ID_ANDROID_SDK:-${ANDROID_HOME:-$HOME/Library/Android/sdk}}"
REQUIRED_NDK_VERSION="27.1.12297006"
ANDROID_NDK_DIR="${ANDROID_NDK_HOME:-$ANDROID_SDK_DIR/ndk/$REQUIRED_NDK_VERSION}"
GRADLE="$WORKSPACE_ROOT/crates/sdk/android/gradlew"
APP_DIR="$SCRIPT_DIR/EuIdBenchAndroid"
PREBUILT_DIR="$APP_DIR/prebuilt"
TARGET_ABI="arm64-v8a"
CARGO_PROFILE="bench"
LTO_MODE="fat"
CODEGEN_UNITS="1"
FEATURES="jni"
BENCHMARK_ENTRYPOINT="fullPq"
BENCHMARK_PROFILE="full_pq_mdoc_mldsa65_ts13_revocation_paired"
REFERENCE_REF="${EU_ID_MLDSA_REFERENCE_REF:-}"

if [[ -z "$REFERENCE_REF" ]]; then
    echo "EU_ID_MLDSA_REFERENCE_REF is required: no canonical Android JNI comparison revision exists in this history" >&2
    exit 1
fi

if [[ -n "${RUSTFLAGS:-}" || -n "${CARGO_ENCODED_RUSTFLAGS:-}" ]]; then
    echo "RUSTFLAGS/CARGO_ENCODED_RUSTFLAGS must be unset for a reproducible benchmark build" >&2
    exit 1
fi

NDK_REVISION="$(
    awk -F= '/^Pkg.Revision/ { value=$2; gsub(/[[:space:]]/, "", value); print value }' \
        "$ANDROID_NDK_DIR/source.properties"
)"
if [[ "$NDK_REVISION" != "$REQUIRED_NDK_VERSION" ]]; then
    echo "Android NDK $REQUIRED_NDK_VERSION is required, got ${NDK_REVISION:-unknown}" >&2
    exit 1
fi

if command -v shasum >/dev/null 2>&1; then
    SHA256=(shasum -a 256)
else
    SHA256=(sha256sum)
fi

hash_file() {
    "${SHA256[@]}" "$1" | awk '{print $1}'
}

hash_stdin() {
    "${SHA256[@]}" | awk '{print $1}'
}

source_hash() {
    local source_root="$1"
    git -C "$source_root" ls-files -c -o --exclude-standard \
        | awk '$0 !~ /\.md$/' \
        | LC_ALL=C sort \
        | while IFS= read -r file; do
            printf '%s  %s\n' "$(hash_file "$source_root/$file")" "$file"
        done \
        | "${SHA256[@]}" \
        | awk '{print $1}'
}

RUSTC_VERSION="$(rustc --version)"
mkdir -p "$PREBUILT_DIR"
REFERENCE_COMMIT="$(git -C "$WORKSPACE_ROOT" rev-parse --verify "$REFERENCE_REF^{commit}")"
CANDIDATE_COMMIT="$(git -C "$WORKSPACE_ROOT" rev-parse --verify 'HEAD^{commit}')"
if [[ "$REFERENCE_COMMIT" == "$CANDIDATE_COMMIT" ]]; then
    echo "reference and candidate commits must differ" >&2
    exit 1
fi
OMITTED_CANDIDATE_CHANGES="$({
    git -C "$WORKSPACE_ROOT" diff --name-only
    git -C "$WORKSPACE_ROOT" diff --cached --name-only
    git -C "$WORKSPACE_ROOT" ls-files -o --exclude-standard
} | awk '$0 !~ /\.md$/' | LC_ALL=C sort -u)"
if [[ -n "$OMITTED_CANDIDATE_CHANGES" ]]; then
    echo "candidate source is committed HEAD $CANDIDATE_COMMIT, but non-Markdown working-tree changes would be omitted:" >&2
    printf '%s\n' "$OMITTED_CANDIDATE_CHANGES" >&2
    exit 1
fi
SOURCE_WORKTREES=()
REFERENCE_SOURCE_SHA256=""
CANDIDATE_SOURCE_SHA256=""

cleanup_source_worktrees() {
    local status="$?"
    trap - EXIT
    local worktree parent
    for worktree in "${SOURCE_WORKTREES[@]}"; do
        parent="$(dirname "$worktree")"
        if [[ "$worktree" == "$PREBUILT_DIR"/.source-*/* ]] \
            && [[ "$(git -C "$worktree" rev-parse --show-toplevel 2>/dev/null || true)" == "$worktree" ]]; then
            git -C "$WORKSPACE_ROOT" worktree remove "$worktree" >/dev/null 2>&1 || true
        fi
        rmdir "$parent" >/dev/null 2>&1 || true
    done
    exit "$status"
}
trap cleanup_source_worktrees EXIT

checkout_source() {
    local slot="$1"
    local commit="$2"
    local parent worktree
    parent="$(mktemp -d "$PREBUILT_DIR/.source-$slot.XXXXXX")"
    worktree="$parent/worktree"
    if ! git -C "$WORKSPACE_ROOT" worktree add --detach "$worktree" "$commit" >/dev/null; then
        rmdir "$parent"
        return 1
    fi
    SOURCE_WORKTREES+=("$worktree")
    CHECKED_OUT_SOURCE="$worktree"
}

build_variant() {
    local slot="$1"
    local variant="$2"
    local commit="$3"
    local output_root="$PREBUILT_DIR/$slot"
    local target_dir="$output_root/cargo-target"
    local library="$output_root/$TARGET_ABI/libeu_id_ffi.so"
    local manifest="$output_root/build-manifest.json"
    local source_root source_sha256 build_id
    checkout_source "$slot" "$commit"
    source_root="$CHECKED_OUT_SOURCE"
    source_sha256="$(source_hash "$source_root")"
    if [[ "$slot" == "mldsa-reference" ]]; then
        REFERENCE_SOURCE_SHA256="$source_sha256"
    else
        CANDIDATE_SOURCE_SHA256="$source_sha256"
        if [[ "$CANDIDATE_SOURCE_SHA256" == "$REFERENCE_SOURCE_SHA256" ]]; then
            echo "reference and candidate source hashes must differ (non-Markdown sources are identical)" >&2
            exit 1
        fi
    fi
    build_id="$(
        printf '%s' \
            "$source_sha256|$commit|$RUSTC_VERSION|$TARGET_ABI|$CARGO_PROFILE|$LTO_MODE|$CODEGEN_UNITS|$FEATURES|$slot|$variant|$NDK_REVISION" \
            | hash_stdin
    )"

    mkdir -p "$output_root"
    (
        cd "$source_root"
        ANDROID_NDK_HOME="$ANDROID_NDK_DIR" \
        CARGO_TARGET_DIR="$target_dir" \
        CARGO_PROFILE_BENCH_LTO="$LTO_MODE" \
        CARGO_PROFILE_BENCH_CODEGEN_UNITS="$CODEGEN_UNITS" \
            cargo ndk -t "$TARGET_ABI" -o "$output_root" \
            build --profile "$CARGO_PROFILE" -p eu-id-ffi --features "$FEATURES"
    )
    test -f "$library"

    local library_sha256
    library_sha256="$(hash_file "$library")"
    printf '%s\n' \
        '{' \
        '  "schema": 1,' \
        "  \"library_slot\": \"$slot\"," \
        "  \"benchmark_variant\": \"$variant\"," \
        "  \"benchmark_entrypoint\": \"$BENCHMARK_ENTRYPOINT\"," \
        "  \"benchmark_profile\": \"$BENCHMARK_PROFILE\"," \
        "  \"build_id\": \"$build_id\"," \
        "  \"source_ref\": \"$commit\"," \
        "  \"git_commit\": \"$commit\"," \
        '  "git_dirty": false,' \
        "  \"source_sha256_no_md\": \"$source_sha256\"," \
        "  \"rustc\": \"$RUSTC_VERSION\"," \
        "  \"target_abi\": \"$TARGET_ABI\"," \
        "  \"ndk_revision\": \"$NDK_REVISION\"," \
        "  \"cargo_profile\": \"$CARGO_PROFILE\"," \
        "  \"features\": [\"$FEATURES\"]," \
        "  \"lto\": \"$LTO_MODE\"," \
        "  \"codegen_units\": $CODEGEN_UNITS," \
        "  \"unstripped_library_sha256\": \"$library_sha256\"" \
        '}' >"$manifest"
}

build_variant "mldsa-reference" "reference" "$REFERENCE_COMMIT"
build_variant "mldsa-candidate" "candidate" "$CANDIDATE_COMMIT"

ANDROID_HOME="$ANDROID_SDK_DIR" \
ANDROID_SDK_ROOT="$ANDROID_SDK_DIR" \
    "$GRADLE" -p "$APP_DIR" assembleRelease \
    -PmldsaReferenceSo="$PREBUILT_DIR/mldsa-reference/$TARGET_ABI/libeu_id_ffi.so" \
    -PmldsaCandidateSo="$PREBUILT_DIR/mldsa-candidate/$TARGET_ABI/libeu_id_ffi.so" \
    -PmldsaReferenceManifest="$PREBUILT_DIR/mldsa-reference/build-manifest.json" \
    -PmldsaCandidateManifest="$PREBUILT_DIR/mldsa-candidate/build-manifest.json"
