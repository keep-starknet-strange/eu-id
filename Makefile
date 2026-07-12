# eu-id — workspace build & developer-tooling entry point.
#
# A single interface shared by contributors and CI. `make check` delegates to
# scripts/check.sh — the single definition of the lint gate, also run by the
# pre-commit hook — so local and CI lint results never diverge.
#
# This branch's product path is quantum-only: ML-DSA issuer, device, and
# revocation authentication. Classical P-256 demo and coprocessor targets live
# on the classical branches.

PROOF ?= proof.bin

# Predicates CLI overrides
DOB      ?=
DATE     ?= $(shell date +%Y-%m-%d)
MIN_AGE  ?= 18
STRATEGY ?= rc

# Nationality predicate overrides
NATIONALITY ?=
ACCEPTABLE  ?=

.DEFAULT_GOAL := help
.PHONY: help dev build test check check-quantum-only-deps fmt perf bench-predicates \
        prove-age verify-age \
        prove-nat verify-nat \
        profile-prove-age-rc profile-verify-age-rc \
        profile-prove-age-bd profile-verify-age-bd \
        publish-android-local publish-android-symbols publish-jvm-local publish-local \
        clean

help:
	@echo "eu-id — workspace make targets"
	@echo ""
	@echo "  make dev           watch sources and re-run cargo check (uses cargo-watch)"
	@echo "  make build         compile the whole workspace"
	@echo "  make test          run the workspace test suite in release mode"
	@echo "  make check         clippy + rustfmt — identical to the CI lint step"
	@echo "  make check-quantum-only-deps  reject classical crypto in the workspace tree"
	@echo "  make fmt           apply rustfmt across the workspace"
	@echo "  make perf          run the full quantum-safe mdoc performance probe"
	@echo "  make bench-predicates  run predicates benchmarks only"
	@echo "  make clean         remove build artifacts"
	@echo ""
	@echo "  make prove-age     run the age predicate prover  (DOB= required)"
	@echo "  make verify-age    run the age predicate verifier"
	@echo ""
	@echo "  prove-age overrides: DOB= DATE= MIN_AGE= STRATEGY=bd|rc PROOF="
	@echo "  verify-age overrides: STRATEGY=bd|rc PROOF="
	@echo ""
	@echo "  make prove-nat     run the nationality predicate prover  (NATIONALITY= ACCEPTABLE= required)"
	@echo "  make verify-nat    run the nationality predicate verifier"
	@echo ""
	@echo "  prove-nat overrides: NATIONALITY= ACCEPTABLE= PROOF="
	@echo "  verify-nat overrides: PROOF="
	@echo ""
	@echo "  make profile-prove-age-rc    profile age prove (range check)"
	@echo "  make profile-verify-age-rc   profile age verify (range check)"
	@echo "  make profile-prove-age-bd    profile age prove (bit decomposition)"
	@echo "  make profile-verify-age-bd   profile age verify (bit decomposition)"
	@echo ""
	@echo "  make publish-android-local   build + publish the SDK AAR to ~/.m2 (mavenLocal)"
	@echo "  make publish-android-symbols build + publish the SDK AAR with a GNU build-id (DWARF"
	@echo "                               already on) so heapprofd/simpleperf traces symbolize"
	@echo "  make publish-jvm-local       build + publish the SDK JVM jar to ~/.m2 (mavenLocal)"
	@echo "  make publish-local           publish both the AAR and the JVM jar to ~/.m2"

dev:
	@if command -v cargo-watch >/dev/null 2>&1; then \
		cargo watch -x check; \
	else \
		echo "dev: cargo-watch not found — running a one-shot check instead"; \
		echo "     (install it with: cargo install cargo-watch)"; \
		cargo check; \
	fi

build:
	cargo build --locked --workspace

test:
	cargo test --locked --workspace --release

check:
	@bash scripts/check.sh

check-quantum-only-deps:
	@bash scripts/check-quantum-only-deps.sh

fmt:
	cargo fmt

perf:
	RAYON_NUM_THREADS=1 cargo run --locked --release -p eu-id-prover --example pq_perf_probe

bench-predicates:
	cargo bench --locked -p predicates

prove-age:
ifndef DOB
	$(error DOB is required, e.g. make prove-age DOB=1990-01-01)
endif
	cargo run --bin prove -- age --dob $(DOB) --date $(DATE) --min-age $(MIN_AGE) --strategy $(STRATEGY) --output $(PROOF)

verify-age:
	cargo run --bin verify -- age --strategy $(STRATEGY) --input $(PROOF)

prove-nat:
ifndef NATIONALITY
	$(error NATIONALITY is required, e.g. make prove-nat NATIONALITY=300 ACCEPTABLE=250,276,300)
endif
ifndef ACCEPTABLE
	$(error ACCEPTABLE is required, e.g. make prove-nat NATIONALITY=300 ACCEPTABLE=250,276,300)
endif
	cargo run --bin prove -- nat --nationality $(NATIONALITY) --acceptable $(ACCEPTABLE) --output $(PROOF)

verify-nat:
	cargo run --bin verify -- nat --input $(PROOF)

profile-prove-age-rc:
	cargo instruments -t Allocations --manifest-path crates/predicates/Cargo.toml --bin prove --release -- age --dob 1990-01-01 --output target/instruments/age-rc.bin

profile-verify-age-rc:
	cargo instruments -t Allocations --manifest-path crates/predicates/Cargo.toml --bin verify --release -- age --input target/instruments/age-rc.bin

profile-prove-age-bd:
	cargo instruments -t Allocations --manifest-path crates/predicates/Cargo.toml --bin prove --release -- age --dob 1990-01-01 --strategy bd --output target/instruments/age-bd.bin

profile-verify-age-bd:
	cargo instruments -t Allocations --manifest-path crates/predicates/Cargo.toml --bin verify --release -- age --strategy bd --input target/instruments/age-bd.bin

# Cross-compile + package the SDK and install it into the local Maven repo
# (~/.m2). Each Gradle project owns its native build (cargo-ndk / cargo-zigbuild)
# and UniFFI binding generation, and stamps the artifact with the workspace
# version (parsed from [workspace.package] in Cargo.toml). Consumers depend on
# the result via `mavenLocal()`.
publish-android-local:
	cd crates/sdk/android && ./gradlew publishToMavenLocal

# Same as publish-android-local, but relinks each .so with a GNU build-id so the
# stripped on-device lib can be matched to the unstripped copy in
# crates/sdk/android/src/main/jniLibs for offline symbolization (Perfetto/heapprofd,
# simpleperf). Toggling the flag changes the cargo build fingerprint, so this forces
# a relink. DWARF is already produced by [profile.release] debug = true.
publish-android-symbols:
	cd crates/sdk/android && ./gradlew publishToMavenLocal -PemitBuildId=true

publish-jvm-local:
	cd crates/sdk/jvm && ./gradlew publishToMavenLocal

publish-local: publish-android-local publish-jvm-local

clean:
	cargo clean
