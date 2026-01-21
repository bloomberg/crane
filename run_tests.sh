#!/bin/bash
# Test runner with cleaner output

set -o pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
CYAN='\033[0;36m'
BOLD='\033[1m'
DIM='\033[2m'
NC='\033[0m' # No Color

# Temporary files
TMPFILE=$(mktemp)
SUMMARY=$(mktemp)
RESULTS_FILE=$(mktemp)
trap "rm -f $TMPFILE $SUMMARY $RESULTS_FILE" EXIT

echo ""
echo -e "${CYAN}${BOLD}Running Crane tests...${NC}"
echo ""

# Check if verbose mode
VERBOSE=false
if [ "${1}" = "-v" ] || [ "${1}" = "--verbose" ]; then
    VERBOSE=true
fi

# Step 1: Clean - Force recompilation
echo -e "${DIM}Cleaning build cache...${NC}"
dune clean 2>/dev/null || true
find _build/default/tests -type f \( -name "*.vo" -o -name "*.vok" -o -name "*.vos" -o -name "*.glob" \) -delete 2>/dev/null || true
echo ""

# Run dune runtest and capture output
if $VERBOSE; then
    # Show all output in verbose mode
    if dune runtest --no-buffer --force 2>&1 | tee "$TMPFILE"; then
        TEST_RESULT=0
    else
        TEST_RESULT=1
    fi
else
    # Real-time mode: show test results as they complete
    echo -e "${CYAN}${BOLD}Running tests...${NC} ${DIM}(use 'make test-verbose' for detailed output)${NC}"
    echo ""

    # Track tests to avoid duplicates
    TESTS_SEEN=$(mktemp)
    TEST_FILE_MAP=$(mktemp)
    trap "rm -f $TMPFILE $SUMMARY $TESTS_SEEN $TEST_FILE_MAP $RESULTS_FILE" EXIT

    # Pre-build a map of test names to file paths by scanning .v files
    echo -e "${DIM}Scanning test files...${NC}"
    while IFS= read -r vfile; do
        # Extract test names from Crane Extraction commands
        # Format: Crane Extraction TestCompile "output_name" Module1 Module2 ...
        # Test ID format: output_name/Module1 and Module2
        while IFS= read -r line; do
            output_name=$(echo "$line" | sed 's/.*"\([^"]*\)".*/\1/')
            identifiers=$(echo "$line" | sed 's/.*"\([^"]*\)"\s*\([^.]*\).*/\2/' | xargs)
            identifier=$(echo "$identifiers" | sed 's/ / and /g')
            if [ -n "$output_name" ] && [ -n "$identifier" ]; then
                # Use format: output_name/identifier to match new test output format
                echo "${output_name}/${identifier}|$vfile" >> "$TEST_FILE_MAP"
            fi
        done < <(grep 'Crane Extraction' "$vfile" 2>/dev/null)
    done < <(find tests -name "*.v" -type f | sort)
    echo ""

    # Function to process a line and extract test result
    process_line() {
        local line="$1"
        local prev_line="$2"
        local prev_prev_line="$3"
        local TEST_NAME=""
        local STATUS_TYPE=""
        local FILE_PATH=""

        # Check for successful extraction - long format
        if echo "$line" | grep -q "✅.*successfully extracted, compiled, and all tests passed\."; then
            TEST_NAME=$(echo "$line" | sed 's/✅ //' | sed 's/ successfully.*//')
            STATUS_TYPE="PASS"
        # Check for successful extraction - short format (just ✅ TestName)
        elif echo "$line" | grep -q "^✅ [^[:space:]]"; then
            TEST_NAME=$(echo "$line" | sed 's/✅ //')
            STATUS_TYPE="PASS"
        # Check for test assertion failures
        elif echo "$line" | grep -q "❌.*extracted and compiled, but test assertions failed\."; then
            TEST_NAME=$(echo "$line" | sed 's/❌ *//' | sed 's/ extracted.*//')
            STATUS_TYPE="FAIL_TEST"
        # Check for compilation failures (single line format)
        elif echo "$line" | grep -q "Error:.*extracted but clang failed to compile"; then
            TEST_NAME=$(echo "$line" | sed 's/.*Error: //' | sed 's/ extracted.*//')
            STATUS_TYPE="FAIL_COMPILE"
            FILE_PATH=$(echo "$prev_line" | grep -o 'File "[^"]*\.v"' | sed 's/File "//; s/"//' | sed 's|^\./||')
        # Check for extraction failures (single line format)
        elif echo "$line" | grep -q "Error:.*failed to extract:"; then
            TEST_NAME=$(echo "$line" | sed 's/.*Error: //' | sed 's/ failed.*//')
            STATUS_TYPE="FAIL_EXTRACT"
            FILE_PATH=$(echo "$prev_line" | grep -o 'File "[^"]*\.v"' | sed 's/File "//; s/"//' | sed 's|^\./||')
        # Check for extraction failures (multi-line format)
        elif echo "$line" | grep -q "^failed to extract:" && echo "$prev_line" | grep -q "^Error:"; then
            TEST_NAME=$(echo "$prev_line" | sed 's/Error: //')
            STATUS_TYPE="FAIL_EXTRACT"
            FILE_PATH=$(echo "$prev_prev_line" | grep -o 'File "[^"]*\.v"' | sed 's/File "//; s/"//' | sed 's|^\./||')
        fi

        if [ -n "$TEST_NAME" ] && [ -n "$STATUS_TYPE" ]; then
            # Check if we've already seen this test
            if ! grep -q "^${TEST_NAME}\$" "$TESTS_SEEN" 2>/dev/null; then
                echo "$TEST_NAME" >> "$TESTS_SEEN"

                # If no file path extracted yet, look it up in the map
                if [ -z "$FILE_PATH" ]; then
                    FILE_PATH=$(grep -i "^${TEST_NAME}|" "$TEST_FILE_MAP" 2>/dev/null | head -1 | cut -d'|' -f2)
                fi

                # Store result for sorting
                printf "%s\t%s\t%s\n" "$TEST_NAME" "$STATUS_TYPE" "$FILE_PATH" >> "$RESULTS_FILE"
                return 0
            fi
        fi
        return 1
    }

    # Function to display sorted results
    display_results() {
        local count=$(grep -c . "$RESULTS_FILE" 2>/dev/null || echo 0)

        # Clear previous display and reposition cursor
        tput clear

        echo ""
        echo -e "${CYAN}${BOLD}Running tests...${NC} ${DIM}(${count} completed)${NC}"
        echo ""

        # Display results table
        COL1_WIDTH=30
        COL2_WIDTH=15
        COL3_WIDTH=45

        printf "${BOLD}%-*s  %-*s  %-*s${NC}\n" $COL1_WIDTH "TEST" $COL2_WIDTH "STATUS" $COL3_WIDTH "FILE"
        printf "%s\n" "$(printf '─%.0s' $(seq 1 95))"

        if [ -f "$RESULTS_FILE" ] && [ -s "$RESULTS_FILE" ]; then
            sort "$RESULTS_FILE" | while IFS=$'\t' read -r test_name status_type file_path; do
                # Convert status type to colored status
                case "$status_type" in
                    PASS)
                        STATUS="${GREEN}PASS           ${NC}"
                        ;;
                    FAIL_TEST)
                        STATUS="${YELLOW}FAIL (test)    ${NC}"
                        ;;
                    FAIL_COMPILE)
                        STATUS="${RED}FAIL (compile)${NC}"
                        ;;
                    FAIL_EXTRACT)
                        STATUS="${RED}FAIL (extract)${NC}"
                        ;;
                    *)
                        STATUS="UNKNOWN        "
                        ;;
                esac

                # Truncate long names/paths
                TEST_NAME_TRUNC="$test_name"
                if [ ${#TEST_NAME_TRUNC} -gt $COL1_WIDTH ]; then
                    TEST_NAME_TRUNC="${TEST_NAME_TRUNC:0:$((COL1_WIDTH-3))}..."
                fi

                FILE_PATH_TRUNC="$file_path"
                if [ ${#FILE_PATH_TRUNC} -gt $COL3_WIDTH ]; then
                    FILE_PATH_TRUNC="...${FILE_PATH_TRUNC: -$((COL3_WIDTH-3))}"
                fi

                # Print row
                printf "%-*s  %b  %-*s\n" \
                    $COL1_WIDTH "$TEST_NAME_TRUNC" \
                    "$STATUS" \
                    $COL3_WIDTH "$FILE_PATH_TRUNC"
            done
        fi

        echo ""
    }

    # Show real-time progress, then final sorted table
    echo -e "${DIM}Tests will be displayed as they complete, followed by sorted summary${NC}"
    echo ""

    PREV_LINE=""
    PREV_PREV_LINE=""

    # Run dune and process output line by line in real-time
    dune runtest --no-buffer --force 2>&1 | while IFS= read -r line; do
        # Always output the line for real-time feedback
        echo "$line" >> "$TMPFILE"

        # Check if this line contains a test result
        if process_line "$line" "$PREV_LINE" "$PREV_PREV_LINE"; then
            # Extract the result for real-time display
            if echo "$line" | grep -q "✅"; then
                echo -e "  ${GREEN}✓${NC} $(echo "$line" | sed 's/✅ //')"
            elif echo "$line" | grep -q "❌"; then
                echo -e "  ${YELLOW}✗${NC} $(echo "$line" | sed 's/❌ //')"
            elif echo "$line" | grep -q "Error:"; then
                echo -e "  ${RED}✗${NC} $(echo "$line" | sed 's/.*Error: //')"
            elif echo "$line" | grep -q "^failed to extract:"; then
                echo -e "  ${RED}✗${NC} $(echo "$PREV_LINE" | sed 's/Error: //')"
            fi
        fi

        PREV_PREV_LINE="$PREV_LINE"
        PREV_LINE="$line"
    done

    TEST_RESULT=${PIPESTATUS[0]}

    # Now display the final sorted table
    echo ""
    echo ""
    echo -e "${CYAN}${BOLD}Final Results (Sorted Alphabetically)${NC}"
    echo ""

    COL1_WIDTH=30
    COL2_WIDTH=15
    COL3_WIDTH=45

    printf "${BOLD}%-*s  %-*s  %-*s${NC}\n" $COL1_WIDTH "TEST" $COL2_WIDTH "STATUS" $COL3_WIDTH "FILE"
    printf "%s\n" "$(printf '─%.0s' $(seq 1 95))"

    if [ -f "$RESULTS_FILE" ] && [ -s "$RESULTS_FILE" ]; then
        sort "$RESULTS_FILE" | while IFS=$'\t' read -r test_name status_type file_path; do
            # Convert status type to colored status
            case "$status_type" in
                PASS)
                    STATUS="${GREEN}PASS           ${NC}"
                    ;;
                FAIL_TEST)
                    STATUS="${YELLOW}FAIL (test)    ${NC}"
                    ;;
                FAIL_COMPILE)
                    STATUS="${RED}FAIL (compile)${NC}"
                    ;;
                FAIL_EXTRACT)
                    STATUS="${RED}FAIL (extract)${NC}"
                    ;;
                *)
                    STATUS="UNKNOWN        "
                    ;;
            esac

            # Truncate long names/paths
            TEST_NAME_TRUNC="$test_name"
            if [ ${#TEST_NAME_TRUNC} -gt $COL1_WIDTH ]; then
                TEST_NAME_TRUNC="${TEST_NAME_TRUNC:0:$((COL1_WIDTH-3))}..."
            fi

            FILE_PATH_TRUNC="$file_path"
            if [ ${#FILE_PATH_TRUNC} -gt $COL3_WIDTH ]; then
                FILE_PATH_TRUNC="...${FILE_PATH_TRUNC: -$((COL3_WIDTH-3))}"
            fi

            # Print row
            printf "%-*s  %b  %-*s\n" \
                $COL1_WIDTH "$TEST_NAME_TRUNC" \
                "$STATUS" \
                $COL3_WIDTH "$FILE_PATH_TRUNC"
        done
    fi

    echo ""
fi

echo ""

# Extract test names and results (sort alphabetically)
# Catch both long format and short format success messages
{ grep "✅.*successfully extracted, compiled, and all tests passed\." "$TMPFILE" | sed 's/✅ //' | sed 's/ successfully.*//' || true; \
  grep "^✅ [^[:space:]]" "$TMPFILE" | sed 's/✅ //' || true; } | sort | uniq > "$SUMMARY.passed"
grep "❌.*extracted and compiled, but test assertions failed\." "$TMPFILE" | sed 's/❌ *//' | sed 's/ extracted.*//' | sort > "$SUMMARY.failed_test" || true
grep "Error:.*extracted but clang failed to compile" "$TMPFILE" | sed 's/.*Error: //' | sed 's/ extracted.*//' | sort > "$SUMMARY.failed_compile" || true
# Catch both single-line and multi-line extraction failures
{ grep "Error:.*failed to extract:" "$TMPFILE" | sed 's/.*Error: //' | sed 's/ failed.*//' || true; \
  grep -B1 "^failed to extract:" "$TMPFILE" | grep "^Error:" | sed 's/Error: //' || true; } | sort | uniq > "$SUMMARY.failed_extract"

# Count results (handling empty files)
PASSED=$(grep -c . "$SUMMARY.passed" 2>/dev/null || echo 0)
FAILED_TEST=$(grep -c . "$SUMMARY.failed_test" 2>/dev/null || echo 0)
FAILED_COMPILE=$(grep -c . "$SUMMARY.failed_compile" 2>/dev/null || echo 0)
FAILED_EXTRACT=$(grep -c . "$SUMMARY.failed_extract" 2>/dev/null || echo 0)
TOTAL=$((PASSED + FAILED_TEST + FAILED_COMPILE + FAILED_EXTRACT))

# Summary
echo ""
echo -e "${BOLD}TEST SUMMARY${NC}"
echo "$(printf '─%.0s' $(seq 1 60))"
echo -e "${GREEN}Passed:${NC}              $(printf "%3d / %3d tests" $PASSED $TOTAL)"
echo -e "${YELLOW}Test failures:${NC}       $(printf "%3d / %3d tests" $FAILED_TEST $TOTAL)"
echo -e "${RED}Compilation failed:${NC}  $(printf "%3d / %3d tests" $FAILED_COMPILE $TOTAL)"
echo -e "${RED}Extraction failed:${NC}   $(printf "%3d / %3d tests" $FAILED_EXTRACT $TOTAL)"
echo ""

# Only show detailed lists in verbose mode (already shown in table otherwise)
if $VERBOSE; then
    # Show passed tests
    if [ $PASSED -gt 0 ]; then
        echo -e "${GREEN}${BOLD}Passed Tests:${NC}"
        while IFS= read -r test; do
            echo -e "  ${GREEN}PASS${NC} ${test}"
        done < "$SUMMARY.passed"
        echo ""
    fi

    # Show test assertion failures
    if [ $FAILED_TEST -gt 0 ]; then
        echo -e "${YELLOW}${BOLD}Test Assertion Failures:${NC} ${DIM}(compiled but assertions failed)${NC}"
        while IFS= read -r test; do
            echo -e "  ${YELLOW}FAIL${NC} ${test}"
        done < "$SUMMARY.failed_test"
        echo ""
    fi

    # Show compilation failures
    if [ $FAILED_COMPILE -gt 0 ]; then
        echo -e "${RED}${BOLD}Compilation Failures:${NC}"
        while IFS= read -r test; do
            echo -e "  ${RED}FAIL${NC} ${test}"
        done < "$SUMMARY.failed_compile"
        echo ""
    fi

    # Show extraction failures
    if [ $FAILED_EXTRACT -gt 0 ]; then
        echo -e "${RED}${BOLD}Extraction Failures:${NC}"
        while IFS= read -r test; do
            echo -e "  ${RED}FAIL${NC} ${test}"
        done < "$SUMMARY.failed_extract"
        echo ""
    fi
fi

# Exit with appropriate code
if [ $FAILED_EXTRACT -gt 0 ] || [ $FAILED_COMPILE -gt 0 ] || [ $FAILED_TEST -gt 0 ]; then
    exit 1
else
    exit 0
fi
