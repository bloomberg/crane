#!/bin/bash
# Run a single test

if [ $# -eq 0 ]; then
    echo "Usage: $0 <test_name>"
    echo ""
    echo "Examples:"
    echo "  $0 list              # Run tests/basics/list/List.v"
    echo "  $0 tree              # Run tests/basics/tree/Tree.v"
    echo "  $0 basics/nat        # Run tests/basics/nat/Nat.v"
    echo "  $0 monadic/iotest    # Run tests/monadic/iotest/IOTest.v"
    echo ""
    echo "Available tests:"
    find tests -name "*.v" -type f | sed 's|tests/||' | sed 's|/[^/]*\.v$||' | sort -u | sed 's/^/  /'
    exit 1
fi

TEST_NAME=$1

# Colors
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[0;33m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m'

# Try to find the test file
# Capitalize first letter for common Coq convention
TEST_NAME_CAP="$(tr '[:lower:]' '[:upper:]' <<< ${TEST_NAME:0:1})${TEST_NAME:1}"

TEST_FILE=""
if [ -f "tests/basics/$TEST_NAME/$TEST_NAME.v" ]; then
    TEST_FILE="tests/basics/$TEST_NAME/$TEST_NAME.v"
elif [ -f "tests/basics/$TEST_NAME/$TEST_NAME_CAP.v" ]; then
    TEST_FILE="tests/basics/$TEST_NAME/$TEST_NAME_CAP.v"
elif [ -f "tests/basics/$TEST_NAME.v" ]; then
    TEST_FILE="tests/basics/$TEST_NAME.v"
elif [ -f "tests/monadic/$TEST_NAME/$TEST_NAME.v" ]; then
    TEST_FILE="tests/monadic/$TEST_NAME/$TEST_NAME.v"
elif [ -f "tests/monadic/$TEST_NAME/$TEST_NAME_CAP.v" ]; then
    TEST_FILE="tests/monadic/$TEST_NAME/$TEST_NAME_CAP.v"
elif [ -f "tests/monadic/$TEST_NAME.v" ]; then
    TEST_FILE="tests/monadic/$TEST_NAME.v"
elif [ -f "tests/wip/$TEST_NAME/$TEST_NAME.v" ]; then
    TEST_FILE="tests/wip/$TEST_NAME/$TEST_NAME.v"
elif [ -f "tests/wip/$TEST_NAME/$TEST_NAME_CAP.v" ]; then
    TEST_FILE="tests/wip/$TEST_NAME/$TEST_NAME_CAP.v"
elif [ -f "tests/wip/$TEST_NAME.v" ]; then
    TEST_FILE="tests/wip/$TEST_NAME.v"
elif [ -f "tests/$TEST_NAME" ]; then
    TEST_FILE="tests/$TEST_NAME"
else
    # Try searching for it in a directory matching the test name
    FOUND=$(find "tests" -type d -name "$TEST_NAME" -exec find {} -name "*.v" -type f \; | head -1)
    if [ -z "$FOUND" ]; then
        # Try case-insensitive search as fallback
        FOUND=$(find tests -iname "${TEST_NAME}.v" -type f | head -1)
    fi
    if [ -n "$FOUND" ]; then
        TEST_FILE="$FOUND"
    else
        echo -e "${RED}Error: Test '$TEST_NAME' not found${NC}"
        echo ""
        echo "Available tests:"
        find tests -name "*.v" -type f | sed 's|tests/||' | sed 's|/[^/]*\.v$||' | sort -u | sed 's/^/  /'
        exit 1
    fi
fi

# Convert to theory name
# Get the actual filename from the filesystem (macOS is case-insensitive)
THEORY_DIR=$(dirname "$TEST_FILE")
ACTUAL_FILE=$(find "$THEORY_DIR" -maxdepth 1 -name "*.v" -type f | head -1)
if [ -n "$ACTUAL_FILE" ]; then
    TEST_BASE=$(basename "$ACTUAL_FILE" .v)
else
    TEST_BASE=$(basename "$TEST_FILE" .v)
fi

# Capitalize first letter for the theory name (Coq convention)
THEORY_NAME="$(tr '[:lower:]' '[:upper:]' <<< ${TEST_BASE:0:1})${TEST_BASE:1}"

echo -e "${CYAN}${BOLD}Running test: ${THEORY_NAME}${NC}"
echo -e "${CYAN}File: ${ACTUAL_FILE:-$TEST_FILE}${NC}"
echo ""

# Build the specific test directory
echo -e "${CYAN}Building test...${NC}"
echo ""

# Capture output
OUTPUT=$(mktemp)
trap "rm -f $OUTPUT" EXIT

# Build just this specific test directory
dune build "$THEORY_DIR" > "$OUTPUT" 2>&1
BUILD_RESULT=$?

# Check if our specific test passed (regardless of overall build result)
if grep -q "✅ ${THEORY_NAME} successfully extracted and compiled" "$OUTPUT" 2>/dev/null; then
    echo -e "${GREEN}${BOLD}✓ ${THEORY_NAME} extracted and compiled successfully${NC}"
    exit 0
elif grep -q "⚠️ ${THEORY_NAME} successfully extracted" "$OUTPUT" 2>/dev/null; then
    echo -e "${YELLOW}${BOLD}⚠ ${THEORY_NAME} compiled with warnings${NC}"
    echo ""
    grep -A3 "${THEORY_NAME}" "$OUTPUT" | head -5
    exit 0
elif grep -q "Error:.*${THEORY_NAME}" "$OUTPUT" 2>/dev/null; then
    # Our specific test failed
    echo -e "${RED}${BOLD}✗ ${THEORY_NAME} failed${NC}"
    echo ""
    grep -A5 -B2 "${THEORY_NAME}" "$OUTPUT" | grep -v "^File.*dune" | head -20
    exit 1
else
    # Couldn't find specific test in output - check if it was already built
    # Extract the base name (lowercase) for checking artifacts
    ARTIFACT_BASE=$(echo "$TEST_BASE" | tr '[:upper:]' '[:lower:]')

    if [ $BUILD_RESULT -eq 0 ]; then
        # Build succeeded - check if artifacts exist
        if [ -f "$THEORY_DIR/${ARTIFACT_BASE}.o" ] || [ -f "$THEORY_DIR/${ARTIFACT_BASE}.t.exe" ]; then
            echo -e "${GREEN}${BOLD}✓ ${THEORY_NAME} already built and compiled successfully${NC}"
            exit 0
        fi
    fi

    # Couldn't determine result
    echo -e "${YELLOW}${BOLD}⚠ Could not determine test result${NC}"
    echo ""
    echo "Searched for: ${THEORY_NAME}"
    echo "Build result: $([ $BUILD_RESULT -eq 0 ] && echo 'success' || echo 'failed')"
    cat "$OUTPUT"
    exit $BUILD_RESULT
fi
