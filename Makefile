# eu-id workspace commands.
#
# Contributors and CI use this interface.
# `make check`, the pre-commit hook, and CI run `scripts/check.sh`.

BUILD_JOBS  ?= 12
PROOF_THREADS ?= 12
TEST_THREADS ?= 1
ALLOW_DIRTY ?= 0
EU_ID_ANDROID_SDK ?= $(HOME)/Library/Android/sdk
REPRO_DIRTY_ARG = $(if $(filter 1,$(ALLOW_DIRTY)),--allow-dirty,)

.DEFAULT_GOAL := help
.PHONY: help dev build test test-ignored check fmt bench-components bench-identity bench-mobile \
        publish-android-local publish-jvm-local publish-local check-reproducible \
        clean

help:
	@echo "eu-id — workspace make targets"
	@echo ""
	@echo "  make dev           Watch source files and run cargo check."
	@echo "  make build         Compile the sole release implementation."
	@echo "  make test          Run the release test suite."
	@echo "  make test-ignored  Run ignored proof and adversarial tests."
	@echo "  make check         Run the CI Clippy and rustfmt checks."
	@echo "  make check-reproducible  Compare two clean release SDK builds."
	@echo "  make fmt           Format the workspace."
	@echo "  make bench-components  Benchmark the SHA-256 and P-256 C ABI."
	@echo "  make bench-identity    Benchmark proveIdentity and verifyIdentity."
	@echo "  make bench-mobile      Build the mobile benchmark."
	@echo "  make clean         Remove build files."
	@echo ""
	@echo "  make publish-android-local   Publish the SDK AAR to the local Maven repository."
	@echo "  make publish-jvm-local       Publish the host-native JVM test JAR locally."
	@echo "  make publish-local           Publish the Android AAR and host-native test JAR locally."
	@echo "  Set ALLOW_DIRTY=1 to label an intentional dirty release build."

dev:
	@if command -v cargo-watch >/dev/null 2>&1; then \
		cargo watch -x check; \
	else \
		echo "dev: cargo-watch not found — running a one-shot check instead"; \
		echo "     (install it with: cargo install cargo-watch)"; \
		cargo check; \
	fi

build:
	CARGO_BUILD_JOBS=$(BUILD_JOBS) RAYON_NUM_THREADS=$(PROOF_THREADS) \
		bash scripts/reproducible-build.sh $(REPRO_DIRTY_ARG) \
		cargo build --locked --workspace --all-targets --release -j $(BUILD_JOBS)

test:
	CARGO_BUILD_JOBS=$(BUILD_JOBS) RAYON_NUM_THREADS=$(PROOF_THREADS) \
		cargo test --locked --workspace --release --all-targets \
		--no-fail-fast -j $(BUILD_JOBS) -- --test-threads=$(TEST_THREADS)

test-ignored:
	CARGO_BUILD_JOBS=$(BUILD_JOBS) RAYON_NUM_THREADS=$(PROOF_THREADS) \
		cargo test --locked --workspace --release --all-targets \
		--no-fail-fast -j $(BUILD_JOBS) -- --ignored --test-threads=$(TEST_THREADS)

check:
	@bash scripts/check.sh

check-reproducible:
	@bash scripts/check-reproducible-build.sh $(REPRO_DIRTY_ARG)

fmt:
	cargo fmt

bench-components:
	CARGO_BUILD_JOBS=$(BUILD_JOBS) RAYON_NUM_THREADS=$(PROOF_THREADS) \
		cargo run --locked --release -j $(BUILD_JOBS) -p eu-id-ffi --example bench_all

bench-identity:
	CARGO_BUILD_JOBS=$(BUILD_JOBS) RAYON_NUM_THREADS=$(PROOF_THREADS) \
		cargo run --locked --release -j $(BUILD_JOBS) -p sdk --example identity_probe

bench-mobile:
	EU_ID_ANDROID_SDK="$(EU_ID_ANDROID_SDK)" bash mobile/build-bench-android.sh

# Build the SDK and publish it to the local Maven repository.
# Each Gradle project builds its native library and UniFFI bindings.
# The published artifact uses the workspace version.
publish-android-local:
	cd crates/sdk/android && ./gradlew publishToMavenLocal -PallowDirtyBuild=$(if $(filter 1,$(ALLOW_DIRTY)),true,false)

publish-jvm-local:
	cd crates/sdk/jvm && ./gradlew publishToMavenLocal -PallowDirtyBuild=$(if $(filter 1,$(ALLOW_DIRTY)),true,false)

publish-local: publish-android-local publish-jvm-local

clean:
	cargo clean
