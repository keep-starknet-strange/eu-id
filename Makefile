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

.DEFAULT_GOAL := help
.PHONY: help dev build run test check fmt bench bench-mobile prove verify clean

help:
	@echo "eu-id — workspace make targets"
	@echo ""
	@echo "  make dev           watch sources and re-run cargo check (uses cargo-watch)"
	@echo "  make build         compile the whole workspace"
	@echo "  make run           run the demo prover CLI"
	@echo "  make test          run the workspace test suite"
	@echo "  make check         clippy + rustfmt — identical to the CI lint step"
	@echo "  make fmt           apply rustfmt across the workspace"
	@echo "  make bench         laptop criterion benchmark suite"
	@echo "  make bench-mobile  mobile (iOS/Android) benchmark harness"
	@echo "  make prove         prove age-over-18 from a sample credential"
	@echo "  make verify        verify a generated proof"
	@echo "  make clean         remove build artifacts"
	@echo ""
	@echo "  prove/verify accept overrides: CREDENTIAL= ISSUER_KEY= PROOF= CURRENT_DATE="

dev:
	@if command -v cargo-watch >/dev/null 2>&1; then \
		cargo watch -x check; \
	else \
		echo "dev: cargo-watch not found — running a one-shot check instead"; \
		echo "     (install it with: cargo install cargo-watch)"; \
		cargo check; \
	fi

build:
	# `--all-targets` covers lib, bins, integration tests, and examples
	# (e.g. `crates/stwo-sha256/examples/prove_demo.rs`), so a compile
	# regression in any of them surfaces in CI's build-test job rather
	# than only when a contributor runs the example.
	cargo build --all-targets

run:
	@if [ -d bin ]; then \
		cargo run --release -p eu-id; \
	else \
		echo "run: demo CLI not implemented yet (bin/ not found)"; \
	fi

test:
	cargo test --workspace

check:
	@bash scripts/check.sh

fmt:
	cargo fmt

bench:
	cargo bench

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

clean:
	cargo clean
