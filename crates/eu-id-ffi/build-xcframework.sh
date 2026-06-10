#!/usr/bin/env bash
# Build the eu-id-ffi static libs for iOS device + simulator and package
# them into EuId.xcframework. Re-run after any change to the Rust crate.
#
# iOS device + simulator targets, packaged as an xcframework (not cargo-lipo).
set -euo pipefail

cd "$(dirname "$0")/../.."   # workspace root

# Extra cargo args, e.g. EXTRA="--features parallel" for multi-threaded
# proving on the phone's cores.
EXTRA="${EXTRA:-}"

TARGETS=(aarch64-apple-ios aarch64-apple-ios-sim)
for t in "${TARGETS[@]}"; do
  echo "building $t ${EXTRA}..."
  cargo build --release -p eu-id-ffi --target "$t" $EXTRA
done

OUT="crates/eu-id-ffi/EuId.xcframework"
rm -rf "$OUT"
xcodebuild -create-xcframework \
  -library "target/aarch64-apple-ios/release/libeu_id_ffi.a"     -headers crates/eu-id-ffi/include/ \
  -library "target/aarch64-apple-ios-sim/release/libeu_id_ffi.a" -headers crates/eu-id-ffi/include/ \
  -output "$OUT"

echo "wrote $OUT"
