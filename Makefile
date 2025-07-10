.PHONY: all build test clean doc fmt clippy audit deny check-all install-tools

# Default target
all: check-all

# Build the project
build:
	cargo build --all-features

# Run tests
test:
	cargo test --all-features
	cargo test --doc --all-features

# Clean build artifacts
clean:
	cargo clean

# Generate documentation
doc:
	cargo doc --no-deps --all-features --open

# Format code
fmt:
	cargo fmt --all

# Run clippy lints
clippy:
	cargo clippy --all-targets --all-features -- -D warnings

# Run security audit
audit:
	cargo audit

# Run cargo-deny checks
deny:
	cargo deny check

# Check with minimal versions
minimal-versions:
	cargo +nightly update -Z minimal-versions
	cargo +nightly check --all-features

# Run miri for undefined behavior detection
miri:
	cargo +nightly miri setup
	cargo +nightly miri test

# Run all checks (recommended before committing)
check-all: fmt clippy test audit deny doc
	@echo "All checks passed!"

# Install development tools
install-tools:
	cargo install cargo-audit
	cargo install cargo-deny
	cargo install cargo-criterion
	cargo install cargo-llvm-cov
	rustup component add miri --toolchain nightly
	rustup component add rustfmt clippy

# Run benchmarks
bench:
	cargo criterion

# Generate coverage report
coverage:
	cargo llvm-cov --all-features --workspace --html

# Check MSRV (Minimum Supported Rust Version)
msrv:
	cargo +1.70 check --all-features

# Release build
release:
	cargo build --release --all-features

# Package for distribution
package:
	cargo package --allow-dirty

# Help target
help:
	@echo "Available targets:"
	@echo "  build          - Build the project"
	@echo "  test           - Run all tests"
	@echo "  clean          - Clean build artifacts"
	@echo "  doc            - Generate and open documentation"
	@echo "  fmt            - Format code"
	@echo "  clippy         - Run clippy lints"
	@echo "  audit          - Run security audit"
	@echo "  deny           - Run cargo-deny checks"
	@echo "  check-all      - Run all checks (recommended)"
	@echo "  install-tools  - Install development tools"
	@echo "  bench          - Run benchmarks"
	@echo "  coverage       - Generate coverage report"
	@echo "  msrv           - Check minimum supported Rust version"
	@echo "  release        - Build release version"
	@echo "  package        - Package for distribution"
	@echo "  help           - Show this help message"