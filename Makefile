.PHONY: build install clean test test-verbose test-sequential test-raw test-one test-list theories plugin all extract quick-test quick-test-one format-test

# Default target: build plugin and theories only (not tests)
build: plugin theories

# Build everything including tests (extract first to avoid race conditions)
all: extract
	dune build

# Extract: build plugin/theories and generate all test C++ files (without compiling them)
# Continues even if some extractions fail (pre-existing plugin bugs)
# Builds all .vo files in a single dune invocation for maximum parallelism
extract: build
	@echo "Extracting all tests..."
	@vo_targets=""; \
	for vfile in tests/*/*/*.v; do \
		if [ -f "$$vfile" ]; then \
			vo_target=$$(echo "$$vfile" | sed 's/\.v$$/.vo/'); \
			vo_targets="$$vo_targets $$vo_target"; \
		fi; \
	done; \
	if [ -n "$$vo_targets" ]; then \
		dune build $$vo_targets 2>/dev/null || true; \
	fi

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

# Build and run tests with formatted summary (parallel)
# extract first to ensure generated .cpp/.h files exist before compiling tests
test: extract
	@./scripts/check-dune-rules.sh
	@dune build bin/test_runner/main.exe
	@./_build/default/bin/test_runner/main.exe

# Build and run tests with verbose error output (parallel)
test-verbose: extract
	@dune build bin/test_runner/main.exe
	@./_build/default/bin/test_runner/main.exe --verbose

# Run tests sequentially (old bash script)
test-sequential:
	@./scripts/run-tests.sh

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

# Fast tests without clang-format (for development iteration)
# Set CRANE_NO_FORMAT=1 to skip formatting during extraction
quick-test: build
	@echo "Extracting all tests (no formatting)..."
	@vo_targets=""; \
	for vfile in tests/*/*/*.v; do \
		if [ -f "$$vfile" ]; then \
			vo_target=$$(echo "$$vfile" | sed 's/\.v$$/.vo/'); \
			vo_targets="$$vo_targets $$vo_target"; \
		fi; \
	done; \
	if [ -n "$$vo_targets" ]; then \
		CRANE_NO_FORMAT=1 dune build $$vo_targets 2>/dev/null || true; \
	fi
	@dune build bin/test_runner/main.exe
	@./_build/default/bin/test_runner/main.exe

# Run a single test without formatting: make quick-test-one TEST=list
quick-test-one:
	@if [ -z "$(TEST)" ]; then \
		echo "Usage: make quick-test-one TEST=<test_name>"; \
		exit 1; \
	fi
	@case "$(TEST)" in \
		*/*)  CRANE_NO_FORMAT=1 dune build @tests/$(TEST)/runtest ;; \
		*)    if [ -d "tests/basics/$(TEST)" ]; then \
		        CRANE_NO_FORMAT=1 dune build @tests/basics/$(TEST)/runtest; \
		      elif [ -d "tests/monadic/$(TEST)" ]; then \
		        CRANE_NO_FORMAT=1 dune build @tests/monadic/$(TEST)/runtest; \
		      elif [ -d "tests/regression/$(TEST)" ]; then \
		        CRANE_NO_FORMAT=1 dune build @tests/regression/$(TEST)/runtest; \
		      else \
		        echo "Test '$(TEST)' not found"; \
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

# Format all generated test .h and .cpp files
# Uses clang-format (LLVM style) for standard tests, bde-format for *_bde tests
format-test:
	@echo "Formatting test files..."
	@find tests -name '*.h' -o -name '*.cpp' | grep -v '\.t\.cpp$$' | grep -v '_bde/' | xargs -P $$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4) clang-format -i -style=LLVM
	@if command -v bde-format >/dev/null 2>&1; then \
		find tests -path '*_bde/*.h' -o -path '*_bde/*.cpp' | grep -v '\.t\.cpp$$' | xargs -P $$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4) bde-format -i; \
	fi
	@echo "Done."

# Clean build artifacts and generated test files
clean:
	@dune clean
	@for category in basics monadic regression wip; do \
		if [ -d "tests/$$category" ]; then \
			for dir in tests/$$category/*/; do \
				if [ -d "$$dir" ]; then \
					name=$$(basename "$$dir"); \
					rm -f "$$dir$$name.cpp" "$$dir$$name.h" "$$dir$$name.o" "$$dir$$name.t.exe"; \
				fi; \
			done; \
		fi; \
	done
	@echo "Cleaned build artifacts and generated test files"

# Help message
help:
	@echo "Crane build system"
	@echo ""
	@echo "Usage:"
	@echo "  make                    - Build plugin and theories (default)"
	@echo "  make extract            - Build + generate all test C++ files"
	@echo "  make test               - Compile and run all tests (parallel)"
	@echo "  make quick-test         - Run all tests without clang-format (fast)"
	@echo "  make quick-test-one TEST=name - Run single test without formatting"
	@echo "  make format-test        - Format all test .h/.cpp files (LLVM style)"
	@echo "  make test-verbose       - Run tests with error details (parallel)"
	@echo "  make test-sequential    - Run tests sequentially (old bash script)"
	@echo "  make test-raw           - Run tests with raw dune output"
	@echo "  make test-one TEST=name - Run a single test (e.g., TEST=list)"
	@echo "  make test-list          - List all available tests"
	@echo "  make all                - Build everything including test executables"
	@echo "  make install            - Install the plugin"
	@echo "  make clean              - Clean build artifacts and generated test files"
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
