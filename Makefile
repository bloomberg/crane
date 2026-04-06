.PHONY: build install clean test test-quick test-verbose test-sequential test-raw test-one test-folder test-folder-verbose test-list theories plugin all extract format

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
	@dune build bin/test_runner/main.exe
	@./_build/default/bin/test_runner/main.exe

# Build and run only tests with changed files (parallel)
# Full extraction runs first, then git diff determines which tests need C++ compile/run
test-quick: extract
	@./scripts/check-dune-rules.sh --fix
	@dune build bin/test_runner/main.exe
	@./_build/default/bin/test_runner/main.exe --changed

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
		*)    found=""; \
		      for cat in basics monadic regression wip; do \
		        if [ -d "tests/$$cat/$(TEST)" ]; then \
		          found="$$cat"; \
		          break; \
		        fi; \
		      done; \
		      if [ -n "$$found" ]; then \
		        dune build @tests/$$found/$(TEST)/runtest; \
		      else \
		        echo "Test '$(TEST)' not found in any category"; \
		        exit 1; \
		      fi ;; \
	esac

# Run all tests in a folder: make test-folder FOLDER=basics
# Examples:
#   make test-folder FOLDER=basics
#   make test-folder FOLDER=monadic
#   make test-folder FOLDER=wip
#   make test-folder FOLDER=regression
test-folder: extract
	@if [ -z "$(FOLDER)" ]; then \
		echo "Usage: make test-folder FOLDER=<folder_name>"; \
		echo ""; \
		echo "Examples:"; \
		echo "  make test-folder FOLDER=basics"; \
		echo "  make test-folder FOLDER=monadic"; \
		echo "  make test-folder FOLDER=wip"; \
		echo "  make test-folder FOLDER=regression"; \
		exit 1; \
	fi
	@if [ ! -d "tests/$(FOLDER)" ]; then \
		echo "Error: Folder 'tests/$(FOLDER)' does not exist"; \
		exit 1; \
	fi
	@dune build bin/test_runner/main.exe
	@./_build/default/bin/test_runner/main.exe --folder $(FOLDER)

# Run all tests in a folder with verbose error output
test-folder-verbose: extract
	@if [ -z "$(FOLDER)" ]; then \
		echo "Usage: make test-folder-verbose FOLDER=<folder_name>"; \
		echo ""; \
		echo "Examples:"; \
		echo "  make test-folder-verbose FOLDER=basics"; \
		echo "  make test-folder-verbose FOLDER=wip"; \
		exit 1; \
	fi
	@if [ ! -d "tests/$(FOLDER)" ]; then \
		echo "Error: Folder 'tests/$(FOLDER)' does not exist"; \
		exit 1; \
	fi
	@dune build bin/test_runner/main.exe
	@./_build/default/bin/test_runner/main.exe --folder $(FOLDER) --verbose

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

# Format source code
format:
	@echo "Formatting C++ test files..."
	@find tests -name '*.t.cpp' -exec clang-format -i {} +
	@echo "Formatting OCaml files..."
	@failed=""; \
	for f in $$(find src bin -name '*.ml' -o -name '*.mli'); do \
		if ! ocamlformat -i "$$f" 2>/dev/null; then \
			failed="$$failed $$f"; \
		fi; \
	done; \
	if [ -n "$$failed" ]; then \
		echo "Warning: ocamlformat could not process:$$failed"; \
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
	@echo "  make                      - Build plugin and theories (default)"
	@echo "  make extract              - Build + generate all test C++ files"
	@echo "  make test                 - Compile and run all tests (parallel)"
	@echo "  make test-quick           - Extract all, compile/run only changed tests"
	@echo "  make test-verbose         - Run tests with error details (parallel)"
	@echo "  make test-sequential      - Run tests sequentially (old bash script)"
	@echo "  make test-raw             - Run tests with raw dune output"
	@echo "  make test-one TEST=name         - Run a single test (e.g., TEST=list)"
	@echo "  make test-folder FOLDER=x       - Run all tests in a folder (e.g., FOLDER=wip)"
	@echo "  make test-folder-verbose FOLDER - Run folder tests with error details"
	@echo "  make test-list                  - List all available tests"
	@echo "  make all                  - Build everything including test executables"
	@echo "  make install              - Install the plugin"
	@echo "  make format               - Format C++ test files and OCaml source"
	@echo "  make clean                - Clean build artifacts and generated test files"
	@echo ""
	@echo "Examples:"
	@echo "  make test-list                     # Show all available tests"
	@echo "  make test-one TEST=list            # Run the list test"
	@echo "  make test-one TEST=tree            # Run the tree test"
	@echo "  make test-one TEST=basics/nat      # Run nat from basics"
	@echo "  make test-one TEST=monadic/io      # Run io from monadic"
	@echo "  make test-folder FOLDER=basics     # Run all basics tests"
	@echo "  make test-folder FOLDER=wip        # Run all wip tests"
	@echo ""
	@echo "Direct dune commands:"
	@echo "  dune build @install - Build plugin and theories only"
	@echo "  dune build          - Build everything including tests"
	@echo "  dune runtest        - Build and run tests"
