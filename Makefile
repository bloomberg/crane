.PHONY: build install clean test test-verbose test-raw test-one test-list theories plugin all

# Default target: build plugin and theories only (not tests)
build: plugin theories

# Build everything including tests
all:
	dune build

# Build just the plugin
plugin:
	dune build src

# Build just the theories
theories:
	dune build theories

# Install the plugin
install:
	dune build @install
	dune install

# Build and run tests
test:
	@./run_tests.sh

# Verbose test output
test-verbose:
	@./run_tests.sh --verbose

# Raw dune test output (no formatting)
test-raw:
	dune runtest --no-buffer

# Run a single test: make test-one TEST=list
test-one:
	@if [ -z "$(TEST)" ]; then \
		echo "Usage: make test-one TEST=<test_name>"; \
		echo ""; \
		echo "Examples:"; \
		echo "  make test-one TEST=list"; \
		echo "  make test-one TEST=tree"; \
		echo "  make test-one TEST=basics/nat"; \
		echo ""; \
		echo "Use 'make test-list' to see all available tests."; \
		exit 1; \
	fi
	@./run_single_test.sh $(TEST)

# List all available tests
test-list:
	@echo "Available tests:"
	@echo ""
	@find tests -name "*.v" -type f | while read f; do \
		dir=$$(dirname "$$f"); \
		base=$$(basename "$$f" .v); \
		base_lower=$$(echo "$$base" | tr '[:upper:]' '[:lower:]'); \
		category=$$(echo "$$dir" | sed 's|tests/||' | sed 's|/.*||'); \
		echo "  $$base_lower ($$category)"; \
	done | sort -u

# Clean build artifacts
clean:
	dune clean

# Help message
help:
	@echo "Crane build system"
	@echo ""
	@echo "Usage:"
	@echo "  make build              - Build plugin and theories (default)"
	@echo "  make all                - Build everything including tests"
	@echo "  make plugin             - Build just the plugin"
	@echo "  make theories           - Build just the theories"
	@echo "  make test               - Build and run all tests (clean summary)"
	@echo "  make test-verbose       - Run tests with detailed output"
	@echo "  make test-raw           - Run tests with raw dune output"
	@echo "  make test-one TEST=name - Run a single test (e.g., TEST=list)"
	@echo "  make test-list          - List all available tests"
	@echo "  make install            - Install the plugin"
	@echo "  make clean              - Clean build artifacts"
	@echo ""
	@echo "Examples:"
	@echo "  make test-list                 # Show all available tests"
	@echo "  make test-one TEST=list        # Run the list test"
	@echo "  make test-one TEST=tree        # Run the tree test"
	@echo "  make test-one TEST=basics/nat  # Run nat from basics"
	@echo ""
	@echo "Direct dune commands:"
	@echo "  dune build @install - Build plugin and theories only"
	@echo "  dune build          - Build everything including tests"
	@echo "  dune runtest        - Build and run tests (raw output)"
