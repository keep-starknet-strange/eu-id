# eu-id — workspace build & developer-tooling entry point.
#
# A single interface shared by contributors and CI. `make check` delegates to
# scripts/check.sh — the single definition of the lint gate, also run by the
# pre-commit hook — so local and CI lint results never diverge.
#
# Some targets drive code that is scaffolded incrementally (the demo CLI in
# bin/, the mobile harness in mobile/). Those targets detect whether the
# backing directory exists: they run the real command once it does, and
# otherwise print a short notice and exit 0. The run/prove/verify targets
# assume the bin/ CLI is the `eu-id` package.

# Paths for the prove/verify demo targets — override on the command line,
# e.g. `make prove CREDENTIAL=path/to/credential.cbor`.
CREDENTIAL   ?= scripts/sample/credential.cbor
ISSUER_KEY   ?= scripts/sample/issuer-key.pub
PROOF        ?= proof.bin
CURRENT_DATE ?= $(shell date +%Y-%m-%d)

# Predicates CLI overrides
DOB      ?=
DATE     ?= $(shell date +%Y-%m-%d)
MIN_AGE  ?= 18
STRATEGY ?= rc

# Nationality predicate overrides
NATIONALITY ?=
ACCEPTABLE  ?=

.DEFAULT_GOAL := help
.PHONY: help dev build run test check fmt bench bench-predicates bench-identity bench-report bench-mobile prove verify \
        prove-age verify-age \
        prove-nat verify-nat \
        profile-prove-age-rc profile-verify-age-rc \
        profile-prove-age-bd profile-verify-age-bd \
        publish-android-local publish-jvm-local publish-local \
        clean

help:
	@echo "eu-id — workspace make targets"
	@echo ""
	@echo "  make dev           watch sources and re-run cargo check (uses cargo-watch)"
	@echo "  make build         compile the whole workspace"
	@echo "  make run           run the demo prover CLI"
	@echo "  make test          run the workspace test suite in release mode"
	@echo "  make check         clippy + rustfmt — identical to the CI lint step"
	@echo "  make fmt           apply rustfmt across the workspace"
	@echo "  make bench             laptop criterion benchmark suite"
	@echo "  make bench-predicates  run predicates benchmarks only"
	@echo "  make bench-identity    criterion benchmark of the combined identity prover"
	@echo "  make bench-report      combined-prover peak-memory + proof-size JSON report"
	@echo "  make bench-mobile      mobile (iOS/Android) benchmark harness"
	@echo "  make prove         prove age-over-18 from a sample credential"
	@echo "  make verify        verify a generated proof"
	@echo "  make clean         remove build artifacts"
	@echo ""
	@echo "  prove/verify accept overrides: CREDENTIAL= ISSUER_KEY= PROOF= CURRENT_DATE="
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
	cargo build --all-targets

run:
	@if [ -d bin ]; then \
		cargo run --release -p eu-id; \
	else \
		echo "run: demo CLI not implemented yet (bin/ not found)"; \
	fi

test:
	cargo test --workspace --release

check:
	@bash scripts/check.sh

fmt:
	cargo fmt

bench:
	cargo bench

bench-predicates:
	cargo bench -p predicates

bench-identity:
	cargo bench -p eu-id-prover

bench-report:
	cargo run --release -p eu-id-prover --example bench_report -- target/bench-report.json

bench-mobile:
	@if [ -d mobile ]; then \
		$(MAKE) -C mobile bench; \
	else \
		echo "bench-mobile: mobile harness not implemented yet (mobile/ not found)"; \
	fi

prove:
	@if [ -d bin ]; then \
		cargo run --release -p eu-id -- prove --credential "$(CREDENTIAL)" --issuer-key "$(ISSUER_KEY)" --out "$(PROOF)"; \
	else \
		echo "prove: demo CLI not implemented yet (bin/ not found)"; \
	fi

verify:
	@if [ -d bin ]; then \
		cargo run --release -p eu-id -- verify --proof "$(PROOF)" --issuer-key "$(ISSUER_KEY)" --current-date "$(CURRENT_DATE)"; \
	else \
		echo "verify: demo CLI not implemented yet (bin/ not found)"; \
	fi

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

publish-jvm-local:
	cd crates/sdk/jvm && ./gradlew publishToMavenLocal

publish-local: publish-android-local publish-jvm-local

clean:
	cargo clean
