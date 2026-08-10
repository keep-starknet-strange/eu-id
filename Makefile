# Workspace commands for the canonical TS13 identity proof.

.DEFAULT_GOAL := help
RAYON_NUM_THREADS ?= 12
.PHONY: help dev build test check check-quantum-only-deps fmt perf \
        publish-android-local publish-jvm-local publish-local clean

help:
	@echo "eu-id — workspace make targets"
	@echo ""
	@echo "  make dev           watch sources and re-run cargo check (uses cargo-watch)"
	@echo "  make build         compile the whole workspace"
	@echo "  make test          run the workspace test suite in release mode"
	@echo "  make check         clippy + rustfmt — identical to the CI lint step"
	@echo "  make check-quantum-only-deps  reject classical crypto in the workspace tree"
	@echo "  make fmt           apply rustfmt across the workspace"
	@echo "  make perf          run the canonical identity API performance probe"
	@echo "  make clean         remove build artifacts"
	@echo ""
	@echo "  make publish-android-local   build + publish the SDK AAR to ~/.m2 (mavenLocal)"
	@echo "  make publish-jvm-local       build + publish the host JVM SDK JAR to ~/.m2"
	@echo "  make publish-local           publish both Android and host JVM SDK packages"

dev:
	@if command -v cargo-watch >/dev/null 2>&1; then \
		cargo watch -x check; \
	else \
		echo "dev: cargo-watch not found — running a one-shot check instead"; \
		echo "     (install it with: cargo install cargo-watch)"; \
		cargo check; \
	fi

build:
	cargo build --locked --workspace --all-targets --release

test:
	RAYON_NUM_THREADS=$(RAYON_NUM_THREADS) cargo test --locked --workspace --release -- --test-threads=1

check:
	@bash scripts/check.sh

check-quantum-only-deps:
	@bash scripts/check-quantum-only-deps.sh

fmt:
	cargo fmt

perf:
	cargo run --locked --release -p sdk --example ts13_sdk_perf_probe

# Build the Android AAR and publish it to the local Maven repository.
publish-android-local:
	cd crates/sdk/android && ./gradlew publishToMavenLocal

# Reuse the Android Gradle wrapper; the JVM project packages only this host's
# native library for wallet unit tests.
publish-jvm-local:
	cd crates/sdk/jvm && ../android/gradlew publishToMavenLocal

publish-local: publish-android-local publish-jvm-local

clean:
	cargo clean
