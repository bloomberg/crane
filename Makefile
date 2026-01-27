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

# Build and run tests with formatted summary
test:
	@./scripts/run-tests.sh

# Build and run tests with verbose error output
test-verbose:
	@./scripts/run-tests.sh --verbose

# Raw dune test output (no formatting)
test-raw:
	dune runtest

# Run a single test: make test-one TEST=list
# Examples:
#   make test-one TEST=list
#   make test-one TEST=basics/nat
#   make test-one TEST=monadic/io
test-one:
	@if [ -z "$(TEST)" ]; then \
		echo "Usage: make test-one TEST=<test_name>"; \
		echo ""; \
		echo "Examples:"; \
		echo "  make test-one TEST=list"; \
		echo "  make test-one TEST=tree"; \
		echo "  make test-one TEST=basics/nat"; \
		echo "  make test-one TEST=monadic/io"; \
		echo ""; \
		echo "Use 'make test-list' to see all available tests."; \
		exit 1; \
	fi
	@# Handle category/test format (e.g., basics/list)
	@case "$(TEST)" in \
		*/*)  dune build @tests/$(TEST)/runtest ;; \
		*)    if [ -d "tests/basics/$(TEST)" ]; then \
		        dune build @tests/basics/$(TEST)/runtest; \
		      elif [ -d "tests/monadic/$(TEST)" ]; then \
		        dune build @tests/monadic/$(TEST)/runtest; \
		      else \
		        echo "Test '$(TEST)' not found in tests/basics/ or tests/monadic/"; \
		        exit 1; \
		      fi ;; \
	esac

# List all available tests
test-list:
	@echo "Available tests:"
	@echo ""
	@echo "basics:"
	@for d in tests/basics/*/; do \
		if [ -f "$${d}"*.t.cpp ]; then \
			echo "  $$(basename $$d)"; \
		fi; \
	done | sort
	@echo ""
	@echo "monadic:"
	@for d in tests/monadic/*/; do \
		if [ -f "$${d}"*.t.cpp ]; then \
			echo "  $$(basename $$d)"; \
		fi; \
	done | sort

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
	@echo "  make test               - Build and run all tests (formatted summary)"
	@echo "  make test-verbose       - Run tests with error details"
	@echo "  make test-raw           - Run tests with raw dune output"
	@echo "  make test-one TEST=name - Run a single test (e.g., TEST=list)"
	@echo "  make test-list          - List all available tests"
	@echo "  make install            - Install the plugin"
	@echo "  make clean              - Clean build artifacts"
	@echo ""
	@echo "Examples:"
	@echo "  make test-list                   # Show all available tests"
	@echo "  make test-one TEST=list          # Run the list test"
	@echo "  make test-one TEST=tree          # Run the tree test"
	@echo "  make test-one TEST=basics/nat    # Run nat from basics"
	@echo "  make test-one TEST=monadic/io    # Run io from monadic"
	@echo ""
	@echo "Direct dune commands:"
	@echo "  dune build @install - Build plugin and theories only"
	@echo "  dune build          - Build everything including tests"
	@echo "  dune runtest        - Build and run tests"
