#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORKSPACE_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
ANDROID_SDK_DIR="${EU_ID_ANDROID_SDK:-${ANDROID_HOME:-$HOME/Library/Android/sdk}}"
REQUIRED_NDK_VERSION="27.1.12297006"
REQUIRED_CARGO_NDK_VERSION="4.1.2"
ANDROID_NDK_DIR="${ANDROID_NDK_HOME:-$ANDROID_SDK_DIR/ndk/$REQUIRED_NDK_VERSION}"
GRADLE="$WORKSPACE_ROOT/crates/sdk/android/gradlew"
REPRO_BUILD="$WORKSPACE_ROOT/scripts/reproducible-build.sh"
APP_DIR="$SCRIPT_DIR/EuIdBenchAndroid"
PREBUILT_DIR="$APP_DIR/prebuilt"
TARGET_ABI="arm64-v8a"
CARGO_PROFILE="release"
PRODUCT_SLOT="sdk-product"
PRODUCT_STATEMENT="sdk_identity_product"

PROFILE_SETTINGS="$(python3 -c '
import pathlib, sys, tomllib
profile = tomllib.loads(pathlib.Path(sys.argv[1]).read_text())["profile"]["release"]
print(profile.get("lto"), profile.get("codegen-units"))
' "$WORKSPACE_ROOT/Cargo.toml")"
if [[ "$PROFILE_SETTINGS" != "fat 1" ]]; then
    echo "release profile must use fat LTO and one codegen unit, got: $PROFILE_SETTINGS" >&2
    exit 1
fi
LTO_MODE="${PROFILE_SETTINGS%% *}"
CODEGEN_UNITS="${PROFILE_SETTINGS##* }"

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
CARGO_NDK_VERSION="$(cargo ndk --version | awk '$1 == "cargo-ndk" { print $2 }')"
if [[ "$CARGO_NDK_VERSION" != "$REQUIRED_CARGO_NDK_VERSION" ]]; then
    echo "cargo-ndk $REQUIRED_CARGO_NDK_VERSION is required, got ${CARGO_NDK_VERSION:-unknown}" >&2
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

BUILD_SCRIPT_SHA256="$(hash_file "$SCRIPT_DIR/build-bench-android.sh")"
GIT_COMMIT="$(git -C "$WORKSPACE_ROOT" rev-parse HEAD)"
if [[ -n "$(git -C "$WORKSPACE_ROOT" status --porcelain)" ]]; then
    GIT_DIRTY=true
else
    GIT_DIRTY=false
fi
SOURCE_SHA256="$(bash "$REPRO_BUILD" --allow-dirty --print-source-id)"
PACKAGING_SOURCE_SHA256="$(
    bash "$REPRO_BUILD" --allow-dirty --print-packaging-source-id
)"
RUSTC_VERSION="$(rustc --version)"

build_product() {
    local output_root="$PREBUILT_DIR/$PRODUCT_SLOT"
    local library="$output_root/$TARGET_ABI/libeuid_zk_sdk.so"
    local manifest="$output_root/build-manifest.json"
    local build_id
    local gnu_build_id
    build_id="$(
        printf '%s' \
            "$SOURCE_SHA256|$PACKAGING_SOURCE_SHA256|$BUILD_SCRIPT_SHA256|$RUSTC_VERSION|$TARGET_ABI|$CARGO_PROFILE|$LTO_MODE|$CODEGEN_UNITS|$PRODUCT_SLOT|mandatory-revocation" \
            "|$NDK_REVISION|$CARGO_NDK_VERSION" \
            | hash_stdin
    )"
    gnu_build_id="${build_id:0:40}"

    mkdir -p "$output_root"
    (
        cd "$WORKSPACE_ROOT"
        ANDROID_NDK_HOME="$ANDROID_NDK_DIR" \
        EUID_BENCH_BUILD_ID="$build_id" \
        EUID_BENCH_LIBRARY_SLOT="$PRODUCT_SLOT" \
        EUID_BENCH_CARGO_PROFILE="$CARGO_PROFILE" \
        EUID_BENCH_LTO="$LTO_MODE" \
        CARGO_TARGET_AARCH64_LINUX_ANDROID_RUSTFLAGS="-C link-arg=-Wl,--no-undefined -C link-arg=-Wl,--build-id=0x$gnu_build_id" \
            bash "$REPRO_BUILD" --allow-dirty \
            cargo ndk -t "$TARGET_ABI" -o "$output_root" \
            rustc --locked --offline -j 12 --profile "$CARGO_PROFILE" -p sdk --lib \
            --features bench-jni --crate-type cdylib
    )
    test -f "$library"

    local library_sha256
    library_sha256="$(hash_file "$library")"
    printf '%s\n' \
        '{' \
        '  "schema": 1,' \
        "  \"library_slot\": \"$PRODUCT_SLOT\"," \
        "  \"statement\": \"$PRODUCT_STATEMENT\"," \
        "  \"build_id\": \"$build_id\"," \
        '  "revocation": true,' \
        "  \"git_commit\": \"$GIT_COMMIT\"," \
        "  \"git_dirty\": $GIT_DIRTY," \
        "  \"source_sha256_no_md\": \"$SOURCE_SHA256\"," \
        "  \"packaging_source_sha256\": \"$PACKAGING_SOURCE_SHA256\"," \
        "  \"build_script_sha256\": \"$BUILD_SCRIPT_SHA256\"," \
        "  \"rustc\": \"$RUSTC_VERSION\"," \
        "  \"target_abi\": \"$TARGET_ABI\"," \
        "  \"ndk_revision\": \"$NDK_REVISION\"," \
        "  \"cargo_ndk\": \"$CARGO_NDK_VERSION\"," \
        "  \"cargo_profile\": \"$CARGO_PROFILE\"," \
        "  \"lto\": \"$LTO_MODE\"," \
        "  \"codegen_units\": $CODEGEN_UNITS," \
        "  \"unstripped_library_sha256\": \"$library_sha256\"" \
        '}' >"$manifest"
}

build_product

ANDROID_HOME="$ANDROID_SDK_DIR" \
ANDROID_SDK_ROOT="$ANDROID_SDK_DIR" \
    "$GRADLE" --offline --no-daemon --max-workers=12 -p "$APP_DIR" assembleRelease \
    -PproductSo="$PREBUILT_DIR/$PRODUCT_SLOT/$TARGET_ABI/libeuid_zk_sdk.so" \
    -PproductManifest="$PREBUILT_DIR/$PRODUCT_SLOT/build-manifest.json"
