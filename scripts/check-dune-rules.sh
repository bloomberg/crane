#!/bin/bash
# Check that dune files have correct test rules for all test directories
# Usage: ./scripts/check-dune-rules.sh [--fix] [--no-prompt]
#
# Checks for:
# - Missing rules: test directories without dune rules (auto-fixed)
# - Orphaned rules: dune rules for non-existent test directories (prompts)
# - Modified rules: existing rules that differ from auto-generated version (prompts)
#
# Options:
#   --fix       Automatically fix all issues without prompting
#   --no-prompt Report issues and exit with error (no interactive prompts)
#
# Default behavior: missing rules are added automatically; prompts for orphaned/modified

set -e

FIX_ALL=false
NO_PROMPT=false

for arg in "$@"; do
    case $arg in
        --fix)
            FIX_ALL=true
            ;;
        --no-prompt)
            NO_PROMPT=true
            ;;
    esac
done

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m'

errors=0

# Prompt user for confirmation
prompt_user() {
    local message=$1
    if [ "$FIX_ALL" = true ]; then
        return 0  # Yes
    fi
    if [ "$NO_PROMPT" = true ]; then
        return 1  # No
    fi
    # Check if stdin is a terminal
    if [ -t 0 ]; then
        echo -en "${BOLD}$message [y/N]: ${NC}"
        read -r response
        case "$response" in
            [yY][eE][sS]|[yY])
                return 0
                ;;
            *)
                return 1
                ;;
        esac
    else
        return 1  # Non-interactive, don't fix
    fi
}

# Extract expected rule for a test from generated output
# Usage: get_expected_rule <test_name>
# Reads from global variable: expected_rules_file
get_expected_rule() {
    local test_name=$1
    local in_rule=false
    local paren_depth=0
    local rule=""

    while IFS= read -r line; do
        if [[ "$line" =~ ^\(subdir\ $test_name$ ]] || [[ "$line" =~ ^\(subdir\ $test_name\  ]]; then
            in_rule=true
            paren_depth=1
            rule="$line"
            continue
        fi

        if [ "$in_rule" = true ]; then
            rule="$rule"$'\n'"$line"
            # Count parentheses
            local opens="${line//[^(]/}"
            local closes="${line//[^)]/}"
            paren_depth=$((paren_depth + ${#opens} - ${#closes}))

            if [ $paren_depth -le 0 ]; then
                break
            fi
        fi
    done < "$expected_rules_file"

    echo "$rule"
}

# Extract a subdir rule from a dune file (returns line numbers too)
extract_rule_with_lines() {
    local dune_file=$1
    local name=$2
    local in_rule=false
    local paren_depth=0
    local start_line=0
    local end_line=0
    local line_num=0

    while IFS= read -r line; do
        line_num=$((line_num + 1))
        if [[ "$line" =~ ^\(subdir\ $name$ ]] || [[ "$line" =~ ^\(subdir\ $name\  ]]; then
            in_rule=true
            paren_depth=1
            start_line=$line_num
            continue
        fi

        if [ "$in_rule" = true ]; then
            # Count parentheses
            local opens="${line//[^(]/}"
            local closes="${line//[^)]/}"
            paren_depth=$((paren_depth + ${#opens} - ${#closes}))

            if [ $paren_depth -le 0 ]; then
                end_line=$line_num
                break
            fi
        fi
    done < "$dune_file"

    echo "$start_line $end_line"
}

# Extract a subdir rule content from a dune file
extract_rule() {
    local dune_file=$1
    local name=$2
    local in_rule=false
    local paren_depth=0
    local rule=""

    while IFS= read -r line; do
        if [[ "$line" =~ ^\(subdir\ $name$ ]] || [[ "$line" =~ ^\(subdir\ $name\  ]]; then
            in_rule=true
            paren_depth=1
            rule="$line"
            continue
        fi

        if [ "$in_rule" = true ]; then
            rule="$rule"$'\n'"$line"
            # Count parentheses
            local opens="${line//[^(]/}"
            local closes="${line//[^)]/}"
            paren_depth=$((paren_depth + ${#opens} - ${#closes}))

            if [ $paren_depth -le 0 ]; then
                break
            fi
        fi
    done < "$dune_file"

    echo "$rule"
}

# Normalize a rule for comparison (remove trailing whitespace, normalize spacing)
normalize_rule() {
    echo "$1" | sed 's/[[:space:]]*$//' | sed '/^$/d'
}

check_category() {
    local category=$1
    local dune_file="$PROJECT_ROOT/tests/$category/dune"

    if [ ! -f "$dune_file" ]; then
        return
    fi

    # Generate all expected rules for this category using gen-test-dune.sh
    expected_rules_file=$(mktemp)
    "$SCRIPT_DIR/gen-test-dune.sh" "$category" > "$expected_rules_file"

    # Get list of test directories (those with .t.cpp files)
    local expected_tests=()
    for dir in "$PROJECT_ROOT/tests/$category"/*/; do
        if [ -d "$dir" ]; then
            local name=$(basename "$dir")
            if [ -f "$dir$name.t.cpp" ]; then
                expected_tests+=("$name")
            fi
        fi
    done

    # Get list of subdir rules in dune file
    local existing_rules=()
    while IFS= read -r line; do
        if [[ "$line" =~ ^\(subdir\ ([a-zA-Z0-9_]+) ]]; then
            existing_rules+=("${BASH_REMATCH[1]}")
        fi
    done < "$dune_file"

    # Find missing rules (tests that exist but have no rule)
    local missing=()
    for test in "${expected_tests[@]}"; do
        local found=false
        for rule in "${existing_rules[@]}"; do
            if [ "$test" = "$rule" ]; then
                found=true
                break
            fi
        done
        if [ "$found" = false ]; then
            missing+=("$test")
        fi
    done

    # Find orphaned rules (rules for tests that don't exist)
    local orphaned=()
    for rule in "${existing_rules[@]}"; do
        local found=false
        for test in "${expected_tests[@]}"; do
            if [ "$test" = "$rule" ]; then
                found=true
                break
            fi
        done
        if [ "$found" = false ]; then
            orphaned+=("$rule")
        fi
    done

    # Collect modified rules (existing rules that differ from expected)
    # Store as: "name|vofile|expected|existing"
    local modified=()
    for test in "${expected_tests[@]}"; do
        # Skip if this test is in the missing list
        local is_missing=false
        for m in "${missing[@]}"; do
            if [ "$test" = "$m" ]; then
                is_missing=true
                break
            fi
        done
        if [ "$is_missing" = true ]; then
            continue
        fi

        # Get expected rule from gen-test-dune.sh output
        local expected=$(get_expected_rule "$test")
        local existing=$(extract_rule "$dune_file" "$test")

        # Normalize and compare
        local norm_expected=$(normalize_rule "$expected")
        local norm_existing=$(normalize_rule "$existing")

        if [ "$norm_expected" != "$norm_existing" ]; then
            modified+=("$test")
        fi
    done

    # Process modified rules (prompt and fix)
    for test in "${modified[@]}"; do
        local expected=$(get_expected_rule "$test")
        local existing=$(extract_rule "$dune_file" "$test")

        echo -e "${CYAN}Modified rule:${NC} $category/$test"
        echo -e "  Expected:"
        echo "$expected" | sed 's/^/    /'
        echo -e "  Actual:"
        echo "$existing" | sed 's/^/    /'

        if prompt_user "Replace with expected rule?"; then
            # Get current line numbers (re-read each time since file may have changed)
            local lines=$(extract_rule_with_lines "$dune_file" "$test")
            local start_line=$(echo "$lines" | cut -d' ' -f1)
            local end_line=$(echo "$lines" | cut -d' ' -f2)

            if [ "$start_line" -gt 0 ] && [ "$end_line" -gt 0 ]; then
                local tmpfile=$(mktemp)
                head -n $((start_line - 1)) "$dune_file" > "$tmpfile"
                echo "$expected" >> "$tmpfile"
                tail -n +$((end_line + 1)) "$dune_file" >> "$tmpfile"
                mv "$tmpfile" "$dune_file"
                echo -e "${GREEN}  -> Replaced rule for $test${NC}"
            fi
        else
            errors=$((errors + 1))
        fi
    done

    # Report and handle missing rules (always add automatically)
    for test in "${missing[@]}"; do
        echo -e "${YELLOW}Missing rule:${NC} $category/$test"

        echo "" >> "$dune_file"
        get_expected_rule "$test" >> "$dune_file"
        echo -e "${GREEN}  -> Added rule for $test${NC}"
    done

    # Report and handle orphaned rules (process in reverse order to preserve line numbers)
    local orphaned_reversed=()
    for ((i=${#orphaned[@]}-1; i>=0; i--)); do
        orphaned_reversed+=("${orphaned[$i]}")
    done

    for rule in "${orphaned_reversed[@]}"; do
        echo -e "${RED}Orphaned rule:${NC} $category/$rule (no test directory exists)"

        if prompt_user "Remove orphaned rule for $rule?"; then
            local lines=$(extract_rule_with_lines "$dune_file" "$rule")
            local start_line=$(echo "$lines" | cut -d' ' -f1)
            local end_line=$(echo "$lines" | cut -d' ' -f2)

            if [ "$start_line" -gt 0 ] && [ "$end_line" -gt 0 ]; then
                # Also remove blank line before if it exists
                if [ "$start_line" -gt 1 ]; then
                    local prev_line=$(sed -n "$((start_line - 1))p" "$dune_file")
                    if [ -z "$prev_line" ]; then
                        start_line=$((start_line - 1))
                    fi
                fi
                sed -i '' "${start_line},${end_line}d" "$dune_file"
                echo -e "${GREEN}  -> Removed rule for $rule${NC}"
            fi
        else
            errors=$((errors + 1))
        fi
    done

    # Clean up temporary file
    rm -f "$expected_rules_file"
}

# Check each category (discovered from tests/ subdirectories)
for category_dir in "$PROJECT_ROOT"/tests/*/; do
    if [ -d "$category_dir" ]; then
        category=$(basename "$category_dir")
        check_category "$category"
    fi
done

if [ $errors -gt 0 ]; then
    echo ""
    echo -e "${YELLOW}$errors issue(s) remain unfixed.${NC}"
    exit 1
fi

echo -e "${GREEN}All dune rules are in sync.${NC}"
