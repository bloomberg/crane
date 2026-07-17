#!/bin/bash
# Run Facebook Infer static analysis on all test C++ files
# Usage: ./scripts/run-infer.sh

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd -P)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd -P)"
THEORIES_CPP="$PROJECT_ROOT/theories/cpp"
TESTS_DIR="$PROJECT_ROOT/tests"

# Infer ships its own clang, so we just need a clang++ on PATH for the
# compiler driver name.  Do NOT pass Homebrew LLVM libc++ include paths or
# -nostdlib++/-stdlib=libc++ flags — they conflict with infer's bundled
# clang-18 headers.
CXX="clang++"
CXX_FLAGS="-std=c++23 -fbracket-depth=1024 -I $THEORIES_CPP"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m'

echo ""
echo -e "${BOLD}Running Infer on Crane test files${NC}"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# Collect all source files
FILES=$(find "$TESTS_DIR" -path '*/wip/*' -prune -o -type f \( -name '*.h' -o -name '*.cpp' -o -name '*.t.cpp' \) -print | sort)

file_count=$(echo "$FILES" | wc -l | tr -d ' ')
echo -e "Found ${CYAN}${file_count}${NC} source files"
echo ""

# Temporary directory for object files
TMPDIR="${TMPDIR:-/tmp}"
OBJ_DIR="$TMPDIR/crane_infer_$$"
mkdir -p "$OBJ_DIR"
# Clean up via a function rather than a trap *string*. A string trap is re-parsed
# as shell code at EXIT, so metacharacters in the (environment-derived) path —
# e.g. a TMPDIR containing ';' or '$(...)' — would be executed. A function body
# expands the quoted path at run time instead; '--' stops a leading-dash path
# being read as an rm option (CWE-78).
cleanup() {
    rm -rf -- "$OBJ_DIR"
}
trap cleanup EXIT

# Clean previous Infer output
rm -rf "$PROJECT_ROOT/infer-out"

# Capture phase: run infer on each file individually
capture_errors=0
file_index=0
for file in $FILES; do
    rel_path="${file#$PROJECT_ROOT/}"
    file_dir="$(dirname "$file")"

    echo -e "  Analyzing ${CYAN}${rel_path}${NC}"

    obj_file="$OBJ_DIR/out_${file_index}.o"
    file_index=$((file_index + 1))

    # Run infer capture for this file.
    # Use --continue so each invocation appends to the capture DB rather
    # than replacing it. The file's own directory is added as an include
    # path so sibling headers resolve.
    if ! infer capture --continue --no-progress-bar -- \
        "$CXX" $CXX_FLAGS -I "$file_dir" -c "$file" -o "$obj_file" 2>/dev/null; then
        echo -e "    ${RED}capture failed${NC}"
        capture_errors=$((capture_errors + 1))
    fi
done

echo ""
echo -e "${BOLD}Running analysis...${NC}"
echo ""

# Analyze all captured files
infer analyze --no-progress-bar

# Print results
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

REPORT="$PROJECT_ROOT/infer-out/report.txt"

# Known false positives: Infer v1.2.0 cannot trace variable reads through
# [&] captures in std::visit lambdas, so it reports DEAD_STORE on:
#   - _loop_*  : loopify shadow variables (tail-recursion loop state)
#   - _x, _x0  : nat/N/Z custom match predecessor bindings in unused branches
#   - n_, m_, fuel_ : similar predecessor bindings in loopified code
#   - f        : function shadow variables in loopified HOFs
# These are all genuinely used but only via lambda captures Infer can't see.
#
# Infer v1.2.0 also reports UNINITIALIZED_VALUE for __param_0 in TMC code:
#   auto _cell = std::make_unique<List<T>>(List<T>::Cons(a0, nullptr));
# Infer cannot trace initialization of `a0` through std::get<> structured
# bindings, so it flags the Cons constructor parameter as uninitialized.
#
# Infer v1.2.0 also reports USE_AFTER_DELETE in two hand-written files due to
# its inability to model std::shared_ptr reference counting:
#   - itree_reified.cpp: itree_bind(m, k) calls m->run() then k(); Infer thinks
#     the shared_ptr destructor deletes the ITree and then k() accesses it, but
#     k() creates a fresh ITree<void>::ret() and never touches m.  Suppressed by
#     "invalidated by `delete` during the call to `itree_bind()`".
#   - stm.cpp: modifyTVar(c, f) takes c by value (copy); when the copy is
#     destroyed, Infer thinks the shared_ptr<VarControlBlock> is freed, but the
#     original c still holds a reference so the control block stays alive.
#     Suppressed by Infer's synthetic field name __infer_backing_count.
SUPPRESS_PATTERN='DEAD_STORE.*"(&_loop_|&_x[0-9]*`|&n_`|&m_`|&fuel_`|&f`)"'

if [ -f "$REPORT" ] && [ -s "$REPORT" ]; then
    # Filter the report: remove suppressed false positives and their context blocks.
    # Each issue in report.txt is a numbered block starting with "#N\n<file>: error:".
    # We suppress blocks whose "written to" line matches the false-positive pattern.
    FILTERED="$PROJECT_ROOT/infer-out/report.filtered.txt"
    python3 - "$REPORT" "$FILTERED" << 'PYEOF'
import sys, re

infile, outfile = sys.argv[1], sys.argv[2]

with open(infile) as f:
    content = f.read()

# Split into issue blocks (each starts with #N on its own line)
blocks = re.split(r'(?=^#\d+$)', content, flags=re.MULTILINE)

# False-positive DEAD_STORE patterns: variable names from [&] lambda capture context
FP_DEAD_STORE_RE = re.compile(
    r"written to `&(_loop_\w+|_x\d*|n_|m_|fuel_|f)`",
)

# False-positive UNINITIALIZED_VALUE pattern: Infer cannot trace initialization
# of values extracted via std::get<> structured bindings into Cons constructors
# in TMC-generated code.  Infer names the constructor parameter __param_0.
FP_UNINIT_RE = re.compile(r"`__param_0\b")

# False-positive USE_AFTER_DELETE patterns: Infer cannot model shared_ptr
# reference counting.
# (1) itree_bind: Infer thinks m is deleted before the continuation runs.
FP_UAD_ITREE_RE = re.compile(
    r"invalidated by `delete` during the call to `itree_bind\(\)`"
)
# (2) TVar modifyTVar: Infer thinks the by-value TVar copy's destructor frees
# the shared control block; __infer_backing_count is its synthetic field name.
FP_UAD_STM_RE = re.compile(r"__infer_backing_count")

kept = []
for block in blocks:
    if block.strip() == '':
        continue
    # Check if this is a DEAD_STORE false positive
    if 'Dead Store' in block and FP_DEAD_STORE_RE.search(block):
        continue  # suppress
    # Check if this is an UNINITIALIZED_VALUE false positive from TMC Cons init
    if 'Uninitialized Value' in block and FP_UNINIT_RE.search(block):
        continue  # suppress
    # Check if this is a USE_AFTER_DELETE false positive from shared_ptr mismodeling
    if 'Use After Delete' in block and (
        FP_UAD_ITREE_RE.search(block) or FP_UAD_STM_RE.search(block)
    ):
        continue  # suppress
    kept.append(block)

with open(outfile, 'w') as f:
    f.write(''.join(kept))
PYEOF

    warning_count=$(grep -c '^#[0-9]' "$FILTERED" 2>/dev/null || echo 0)
    suppressed=$(grep -c '^#[0-9]' "$REPORT" 2>/dev/null || echo 0)
    suppressed=$((suppressed - warning_count))

    if [ "$warning_count" -gt 0 ]; then
        echo -e "${BOLD}${RED}Infer warnings:${NC}"
        echo ""
        cat "$FILTERED"
        echo ""
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        echo -e "${BOLD}${RED}${warning_count} warning(s) found${NC} (${suppressed} known false positives suppressed)"
    else
        echo -e "${BOLD}${GREEN}No warnings found${NC} (${suppressed} known false positives suppressed)"
    fi
else
    echo -e "${BOLD}${GREEN}No warnings found${NC}"
fi

if [ $capture_errors -gt 0 ]; then
    echo -e "${RED}${capture_errors} file(s) failed to capture${NC}"
fi

echo ""
