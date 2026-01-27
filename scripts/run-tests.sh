#!/bin/bash
# Run tests and format output as a summary table
# Usage: ./scripts/run-tests.sh [--verbose]

set -o pipefail

VERBOSE=false
if [ "$1" = "--verbose" ] || [ "$1" = "-v" ]; then
    VERBOSE=true
fi

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m' # No Color

# Temp files for results
TMPDIR="${TMPDIR:-/tmp}"
RESULTS_FILE="$TMPDIR/crane_test_results_$$"
ERRORS_DIR="$TMPDIR/crane_test_errors_$$"
mkdir -p "$ERRORS_DIR"
trap "rm -rf $RESULTS_FILE $ERRORS_DIR" EXIT

# Print header
echo ""
echo -e "${BOLD}Running Crane Tests${NC}"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

total=0
passed=0
failed=0

# Run tests for a category
run_category() {
    local category=$1
    echo -e "${CYAN}${category}/${NC}"

    for dir in tests/${category}/*/; do
        if [ -d "$dir" ]; then
            name=$(basename "$dir")
            # Check if it has a test file
            if ls "$dir"*.t.cpp >/dev/null 2>&1; then
                printf "  %-25s " "$name"

                output=$(dune build @tests/${category}/${name}/runtest 2>&1)
                exit_code=$?

                total=$((total + 1))

                if [ $exit_code -eq 0 ]; then
                    echo -e "${GREEN}✓ pass${NC}"
                    passed=$((passed + 1))
                else
                    echo -e "${RED}✗ fail${NC}"
                    failed=$((failed + 1))
                    # Save error for verbose mode
                    echo "$output" > "$ERRORS_DIR/${category}_${name}"
                fi
            fi
        fi
    done
}

# Run all categories
run_category "basics"
echo ""
run_category "monadic"

# Print summary
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
if [ $failed -eq 0 ]; then
    echo -e "${BOLD}${GREEN}All $total tests passed${NC}"
else
    echo -e "${BOLD}Results: ${GREEN}$passed passed${NC}, ${RED}$failed failed${NC}, $total total"
fi
echo ""

# Print errors in verbose mode
if [ "$VERBOSE" = true ] && [ $failed -gt 0 ]; then
    echo -e "${BOLD}${RED}Failed test details:${NC}"
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    for errfile in "$ERRORS_DIR"/*; do
        if [ -f "$errfile" ]; then
            name=$(basename "$errfile" | tr '_' '/')
            echo ""
            echo -e "${YELLOW}[$name]${NC}"
            head -40 "$errfile"
            lines=$(wc -l < "$errfile")
            if [ "$lines" -gt 40 ]; then
                echo "... ($(($lines - 40)) more lines)"
            fi
        fi
    done
fi

# Exit with appropriate code
if [ $failed -gt 0 ]; then
    exit 1
fi
exit 0
