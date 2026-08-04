#!/usr/bin/env bash
# Build the `eu-id-ffi` static libraries for iOS devices and simulators.
# Then package the libraries in `EuId.xcframework`.
# Run this script after each Rust crate change.
#
# Package the iOS device and simulator targets as an XCFramework.
set -euo pipefail

cd "$(dirname "$0")/../.."   # workspace root

TARGET_DIR="${CARGO_TARGET_DIR:-target}"
if [[ "$TARGET_DIR" != /* ]]; then
  TARGET_DIR="$PWD/$TARGET_DIR"
fi

REPRO_ARGS=()
if [[ "${EUID_ALLOW_DIRTY_BUILD:-0}" == "1" ]]; then
  REPRO_ARGS=(--allow-dirty)
fi

# Use the iOS application deployment target.
# Otherwise, Rust uses iOS 10 and can conflict with the selected Xcode SDK.
export IPHONEOS_DEPLOYMENT_TARGET="${IPHONEOS_DEPLOYMENT_TARGET:-17.0}"

TARGETS=(aarch64-apple-ios aarch64-apple-ios-sim)
for t in "${TARGETS[@]}"; do
  echo "building $t..."
  bash scripts/reproducible-build.sh "${REPRO_ARGS[@]}" \
    cargo rustc --locked --offline --release -j 12 -p eu-id-ffi --lib \
    --target "$t" --crate-type staticlib
done

OUT="crates/eu-id-ffi/EuId.xcframework"
rm -rf "$OUT"
bash scripts/reproducible-build.sh "${REPRO_ARGS[@]}" \
  xcodebuild -create-xcframework \
  -library "$TARGET_DIR/aarch64-apple-ios/release/libeu_id_ffi.a"     -headers crates/eu-id-ffi/include/ \
  -library "$TARGET_DIR/aarch64-apple-ios-sim/release/libeu_id_ffi.a" -headers crates/eu-id-ffi/include/ \
  -output "$OUT"

echo "wrote $OUT"
