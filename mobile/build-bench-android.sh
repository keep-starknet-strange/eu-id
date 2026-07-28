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
    git -C "$WORKSPACE_ROOT" ls-files -c -o --exclude-standard \
        | awk '$0 !~ /\.md$/' \
        | LC_ALL=C sort \
        | while IFS= read -r file; do
            printf '%s  %s\n' "$(hash_file "$WORKSPACE_ROOT/$file")" "$file"
        done \
        | "${SHA256[@]}" \
        | awk '{print $1}'
}

GIT_COMMIT="$(git -C "$WORKSPACE_ROOT" rev-parse HEAD)"
if [[ -n "$(git -C "$WORKSPACE_ROOT" status --porcelain)" ]]; then
    GIT_DIRTY=true
else
    GIT_DIRTY=false
fi
SOURCE_SHA256="$(source_hash)"
RUSTC_VERSION="$(rustc --version)"

build_variant() {
    local slot="$1"
    local revocation_mode="$2"
    local statement="$3"
    local output_root="$PREBUILT_DIR/$slot"
    local library="$output_root/$TARGET_ABI/libeuid_zk_sdk.so"
    local manifest="$output_root/build-manifest.json"
    local build_id
    build_id="$(
        printf '%s' \
            "$SOURCE_SHA256|$RUSTC_VERSION|$TARGET_ABI|$CARGO_PROFILE|$LTO_MODE|$CODEGEN_UNITS|$slot|$revocation_mode" \
            "|$NDK_REVISION" \
            | hash_stdin
    )"

    mkdir -p "$output_root"
    (
        cd "$WORKSPACE_ROOT"
        ANDROID_NDK_HOME="$ANDROID_NDK_DIR" \
        EUID_BENCH_TS13_REVOCATION="$revocation_mode" \
        EUID_BENCH_BUILD_ID="$build_id" \
        EUID_BENCH_LIBRARY_SLOT="$slot" \
        EUID_BENCH_CARGO_PROFILE="$CARGO_PROFILE" \
        EUID_BENCH_LTO="$LTO_MODE" \
        CARGO_PROFILE_BENCH_LTO="$LTO_MODE" \
        CARGO_PROFILE_BENCH_CODEGEN_UNITS="$CODEGEN_UNITS" \
            cargo ndk -t "$TARGET_ABI" -o "$output_root" \
            build --profile "$CARGO_PROFILE" -p sdk --features bench-jni
    )
    test -f "$library"

    local library_sha256
    library_sha256="$(hash_file "$library")"
    printf '%s\n' \
        '{' \
        '  "schema": 1,' \
        "  \"library_slot\": \"$slot\"," \
        "  \"statement\": \"$statement\"," \
        "  \"build_id\": \"$build_id\"," \
        "  \"revocation_mode\": \"$revocation_mode\"," \
        "  \"git_commit\": \"$GIT_COMMIT\"," \
        "  \"git_dirty\": $GIT_DIRTY," \
        "  \"source_sha256_no_md\": \"$SOURCE_SHA256\"," \
        "  \"rustc\": \"$RUSTC_VERSION\"," \
        "  \"target_abi\": \"$TARGET_ABI\"," \
        "  \"ndk_revision\": \"$NDK_REVISION\"," \
        "  \"cargo_profile\": \"$CARGO_PROFILE\"," \
        "  \"lto\": \"$LTO_MODE\"," \
        "  \"codegen_units\": $CODEGEN_UNITS," \
        "  \"unstripped_library_sha256\": \"$library_sha256\"" \
        '}' >"$manifest"
}

# Legacy slot names are retained only for APK/UI compatibility. Their
# manifests and native result JSON identify the statements they actually run.
build_variant \
    "p256-range16" \
    "1" \
    "ts13_n1_age_over_18_revocation"
build_variant \
    "p256-range8" \
    "0" \
    "ts13_n1_age_over_18_no_revocation"

ANDROID_HOME="$ANDROID_SDK_DIR" \
ANDROID_SDK_ROOT="$ANDROID_SDK_DIR" \
    "$GRADLE" -p "$APP_DIR" assembleRelease \
    -Pp256Range16So="$PREBUILT_DIR/p256-range16/$TARGET_ABI/libeuid_zk_sdk.so" \
    -Pp256Range8So="$PREBUILT_DIR/p256-range8/$TARGET_ABI/libeuid_zk_sdk.so" \
    -Pp256Range16Manifest="$PREBUILT_DIR/p256-range16/build-manifest.json" \
    -Pp256Range8Manifest="$PREBUILT_DIR/p256-range8/build-manifest.json"
