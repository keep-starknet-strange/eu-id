set -euo pipefail

cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

cargo clippy --locked --workspace --all-targets --release -- -D warnings
cargo fmt --all -- --check
