#!/usr/bin/env bash
# Build the host SDK twice in distinct target directories and compare artifacts.
set -euo pipefail

workspace_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
allow_dirty=()
if [[ "${1:-}" == "--allow-dirty" ]]; then
    allow_dirty=(--allow-dirty)
    shift
fi
if [[ $# -ne 0 ]]; then
    echo "usage: $0 [--allow-dirty]" >&2
    exit 2
fi

host_target="$(rustc -vV | awk '/^host:/ { print $2 }')"
release_profile="$(python3 -c '
import pathlib, sys, tomllib
p = tomllib.loads(pathlib.Path(sys.argv[1]).read_text())["profile"]["release"]
print(p.get("lto"), p.get("codegen-units"))
' "$workspace_root/Cargo.toml")"
if [[ "$release_profile" != "fat 1" ]]; then
    echo "release profile must use fat LTO and one codegen unit, got: $release_profile" >&2
    exit 1
fi
case "$host_target" in
    *-apple-darwin)
        artifacts=(
            release/libeuid_zk_sdk.dylib
            release/libeuid_zk_sdk.a
            release/examples/identity_probe
        )
        target_rustflags_name="CARGO_TARGET_$(
            printf '%s' "$host_target" | tr '[:lower:]-' '[:upper:]_'
        )_RUSTFLAGS"
        library_rustflags="-C link-arg=-Wl,-no_uuid -C link-arg=-Wl,-install_name,@rpath/libeuid_zk_sdk.dylib"
        # Mach-O executables require LC_UUID. Apple ld derives it from content.
        probe_rustflags="-C link-arg=-Wl,-install_name,@rpath/libeuid_zk_sdk.dylib"
        ;;
    *-unknown-linux-gnu)
        artifacts=(
            release/libeuid_zk_sdk.so
            release/libeuid_zk_sdk.a
            release/examples/identity_probe
        )
        target_rustflags_name=""
        library_rustflags=""
        probe_rustflags=""
        ;;
    *)
        echo "unsupported reproducibility-check host: $host_target" >&2
        exit 1
        ;;
esac

scratch="$(mktemp -d "${TMPDIR:-/tmp}/eu-id-repro.XXXXXX")"
case "$scratch" in
    "${TMPDIR:-/tmp}"/eu-id-repro.*) ;;
    *) echo "unexpected temporary path: $scratch" >&2; exit 1 ;;
esac
trap 'rm -rf -- "$scratch"' EXIT
# Apple ld's content UUID is sensitive to LTO target-path length.
first_target_dir="$scratch/target-a"
second_target_dir="$scratch/target-b"

build_crate_type() {
    local crate_type="$1"
    local target_dir="$2"
    local -a command=(
        env
        "CARGO_TARGET_DIR=$target_dir"
    )
    if [[ -n "$target_rustflags_name" ]]; then
        command+=("$target_rustflags_name=$library_rustflags")
    fi
    command+=(
        bash "$workspace_root/scripts/reproducible-build.sh" "${allow_dirty[@]}"
        cargo rustc --locked --offline --release -j 12 -p sdk --lib
        --target "$host_target" --crate-type "$crate_type"
    )
    "${command[@]}"
}

build_probe() {
    local target_dir="$1"
    local -a command=(
        env
        "CARGO_TARGET_DIR=$target_dir"
    )
    if [[ -n "$target_rustflags_name" ]]; then
        command+=("$target_rustflags_name=$probe_rustflags")
    fi
    command+=(
        bash "$workspace_root/scripts/reproducible-build.sh" "${allow_dirty[@]}"
        cargo build --locked --offline --release -j 12 -p sdk
        --target "$host_target" --example identity_probe
    )
    "${command[@]}"
}

build_once() {
    local target_dir="$1"
    # Cargo omits LTO when one invocation emits rlib and final library types.
    # Build each shipped type separately so the release LTO profile applies.
    build_crate_type cdylib "$target_dir"
    build_crate_type staticlib "$target_dir"
    build_probe "$target_dir"
}

source_id_before="$(
    bash "$workspace_root/scripts/reproducible-build.sh" \
        "${allow_dirty[@]}" --print-source-id
)"
packaging_source_id_before="$(
    bash "$workspace_root/scripts/reproducible-build.sh" \
        "${allow_dirty[@]}" --print-packaging-source-id
)"
build_once "$first_target_dir"
build_once "$second_target_dir"
source_id_after="$(
    bash "$workspace_root/scripts/reproducible-build.sh" \
        "${allow_dirty[@]}" --print-source-id
)"
packaging_source_id_after="$(
    bash "$workspace_root/scripts/reproducible-build.sh" \
        "${allow_dirty[@]}" --print-packaging-source-id
)"
if [[ "$source_id_before" != "$source_id_after" ]]; then
    echo "source inputs changed between reproducibility builds" >&2
    exit 1
fi
if [[ "$packaging_source_id_before" != "$packaging_source_id_after" ]]; then
    echo "packaging inputs changed between reproducibility builds" >&2
    exit 1
fi

if command -v shasum >/dev/null 2>&1; then
    sha256=(shasum -a 256)
else
    sha256=(sha256sum)
fi
for artifact in "${artifacts[@]}"; do
    first="$first_target_dir/$host_target/$artifact"
    second="$second_target_dir/$host_target/$artifact"
    cmp "$first" "$second"
    if [[ "$host_target" == *-apple-darwin && \
        "$artifact" == release/examples/identity_probe && \
        -z "$(dwarfdump --uuid "$second")" ]]; then
        echo "identity_probe requires a Mach-O UUID" >&2
        exit 1
    fi
    hash="$("${sha256[@]}" "$second" | awk '{ print $1 }')"
    bytes="$(wc -c <"$second" | tr -d ' ')"
    echo "$(basename "$artifact") source=$source_id_after packaging_source=$packaging_source_id_after sha256=$hash bytes=$bytes"
done
