#!/usr/bin/env bash
# Check the dependency direction between the plugin's directories, which
# follow the IRs and the pipeline: the IR grammars depend on no stage, each
# stage only on the IRs and the stages below it, and the printer on neither
# lowering nor the passes before the erasure seam.  Direct dependencies are
# checked; each directory obeying the rule keeps the transitive closure
# obeying it too.  The printer also asks Table nothing about the program
# beyond a list that only shrinks, wherever in the plugin the read is written
# (bin/printer_reads, which needs OCaml's compiler-libs, finds them).
#
# Usage: scripts/check-module-deps.sh   (from the repository root)
set -euo pipefail
cd "$(dirname "$0")/.."

# The directories of src/, lowest first.  A directory is one node of the
# dependency graph (src/core/ is the namespace Core): a module outside it
# that names it depends on all of it.  Each may name only the directories
# before it here.
LAYERS=(
  core            # Core IR
  control_ir      # ControlIR
  cpp_ir          # CppIR, and the C++ target's vocabulary
  base            # Table, probes, ids, helpers spanning Core and CppIR
  core_passes     # Core -> Core
  rocq_to_core    # Rocq -> Core
  core_plan       # analyses of Core that make the unit's plan
  core_to_control # Core -> ControlIR
  unit_plan       # the unit's context and its planned names
  ownership_ir    # OwnershipIR
  cpp_ast         # CppAST
  cpp_passes      # CppIR Lowered -> Resolved
  control_to_cpp  # ControlIR -> CppIR
  core_to_cpp     # Core -> CppIR
  emit            # printing and file layout
  driver          # the extraction driver
)
cap() { printf '%s' "${1:0:1}" | tr '[:lower:]' '[:upper:]'; printf '%s' "${1:1}"; }

# Core elaboration plans calls, matches and spines before lowering runs, on
# Core terms, their Core types and the table: it names no C++
# representation.  Base.Type_util, which it reads, depends on CppIR, so the
# rule is about these modules' own code.
CORE_PLANNING="core_plan/query core_plan/elaborate core_plan/match_kind core_passes/spines core_passes/numeral_literal core_plan/elaborated_call core_plan/instance_methods core/positional"

# file : forbidden names (directories, or siblings in its own directory)
rules=(
  # The C++ target's vocabulary and the Core helpers below Table depend on
  # nothing of the compiler but the IR they are about.
  "emit/backend cpp_ir/foreign_template cpp_ir/crane_rt cpp_ir/tparam_kinds core/scheme core/lexenv : Base"
  "$CORE_PLANNING : Cpp_ir"
  # The printer reads the settled declarations the erasure seam hands it
  # (Cpp_passes.Erasure); nothing of lowering, the other finishing passes,
  # or the drivers around it.
  "emit/print : Core_to_cpp Control_to_cpp Core_to_control Ownership_ir Driver Files Entities Function_entity"
)
# What the printer may name of Cpp_passes.
PRINTER_PASSES="Erasure"

# The printer reads Table for configuration and for spelling rules that are
# functions of a name alone (what it records under CRANE_CHECK_IR -- the
# headers and customs it writes -- it records in an oracle's branch); a fact
# about the program it is handed in the declaration, decided by a plan or a
# pass.  The
# facts it still asks Table for are listed, and the list only shrinks: a read
# that goes is deleted from it, and a new one is an error.
#
# A read counts wherever it is written: in emit/print.ml (which opens Table,
# so a read need not be qualified), or in any value of the plugin a value of
# emit/print.ml reaches.  bin/printer_reads lists them from the typed trees
# dune writes, with a shortest chain each; a read in the branch of an
# [if Base.Probe.checking () then] is an oracle's and does not count.  The graph
# does not follow control flow: a naming function the printer shares with
# the resolver must not refer to the resolver's live naming at all, which
# reaches it through the namers it hands the position
# (Unit_plan.Cpp_state.live_namers), or every read of live naming counts.  Given a
# fourth argument, bin/printer_reads lists every edge by which the printer
# reaches that value of Table, not one chain: all of them must go for the
# read to.
PRINTER_TABLE_CONFIGURATION="arena_header erase_fn_header escape_reserved_struct_name std_lib"
# Facts the printer reads that planning should hand it: none left.
PRINTER_TABLE_PENDING=""

status=0
# CppIR reaches the resolved phase one way: Cpp_passes.Pipeline, which
# finishes a declaration and resolves the few types and values written
# outside every declaration.  No other module converts (Cpp_ir.Resolve), and
# the printer and the CppAST it reads name no lowered value.
while IFS= read -r f; do
  case "$f" in src/cpp_passes/pipeline.ml) continue ;; esac
  if grep -q 'Cpp_ir\.Resolve\b' "$f"; then
    echo "$f converts CppIR to the resolved phase (Cpp_ir.Resolve), which only Cpp_passes.Pipeline may"
    status=1
  fi
done < <(find src -name '*.ml' -o -name '*.mli' | grep -v '^src/_build')
for f in src/emit/print.ml src/emit/print.mli src/cpp_ast/cpp_ast.ml src/cpp_ast/cpp_ast.mli; do
  if grep -q 'Cpp_ir\.Lowered\b\|Grammar\.lowered\b' "$f"; then
    echo "$f names a lowered CppIR value, which the printer may not read"
    status=1
  fi
done
# The code of a file, its (nested) comments removed.
code_of() { perl -0777 -pe 's/(\(\*(?:[^(*]|\((?!\*)|\*(?!\))|(?1))*\*\))//gs' "$1"; }
passes=$(for f in src/emit/print.ml src/emit/print.mli; do code_of "$f"; done \
  | grep -o 'Cpp_passes\.[A-Z][A-Za-z_]*' | cut -d. -f2 | sort -u | grep -vxF "$PRINTER_PASSES" || true)
if [[ -n "$passes" ]]; then
  echo "the printer names a finishing pass other than $PRINTER_PASSES: $passes"
  status=1
fi

deps_of() { ocamlfind ocamldep -modules "$1" | cut -d: -f2; }

# Lowering builds the coercion vocabulary (Function_value, Erase_callable,
# Box, Any_cast, Tolerant_any_cast, and Erasure's box/unbox helpers) only in
# Core_to_cpp.Coerce; Cpp_passes.Coercions expands the plans it makes.  A
# constructor counts where it is applied outside a pattern.  The other
# lowering files that still build one are listed with their count, and the
# list only shrinks: a count that drops is lowered here, a new site is an
# error (typed CppIR design, phase D).
COERCION_BUILDERS_PENDING="core_to_cpp/match.ml:1"
coercion_builders() {
  code_of "$1" | perl -0777 -ne '$n = 0;
    while (/(\S+)\s*\b(?:(?:Cpp_ir\.)?(?:Lowered\.)?(?:Expr\.)?(?:Function_value|Erase_callable|Box|Any_cast|Tolerant_any_cast)\s*\(|Erasure\.(?:box|unbox|unbox_tolerant)\b)/g) {
      $n++ unless $1 =~ /^(\||with|function|as|_,)$/ }
    print $n'
}
for f in src/core_to_cpp/*.ml src/control_to_cpp/*.ml; do
  case "$f" in src/core_to_cpp/coerce.ml) continue ;; esac
  n=$(coercion_builders "$f")
  rel=${f#src/}
  allowed=0
  for e in $COERCION_BUILDERS_PENDING; do
    [[ "${e%%:*}" == "$rel" ]] && allowed=${e##*:}
  done
  if (( n > allowed )); then
    echo "$f builds a coercion $n times ($allowed allowed): build it with Core_to_cpp.Coerce"
    status=1
  elif (( n < allowed )); then
    echo "$f builds a coercion $n times: lower its count in COERCION_BUILDERS_PENDING to $n"
    status=1
  fi
done


# Every directory names only the directories below it.
for i in "${!LAYERS[@]}"; do
  dir=${LAYERS[$i]}
  if [[ ! -d "src/$dir" ]]; then
    echo "src/$dir does not exist: update LAYERS"
    status=1
    continue
  fi
  above=" "
  for j in "${!LAYERS[@]}"; do
    if (( j > i )); then above+="$(cap "${LAYERS[$j]}") "; fi
  done
  for f in src/"$dir"/*.ml src/"$dir"/*.mli; do
    for d in $(deps_of "$f"); do
      if [[ "$above" == *" $d "* ]]; then
        echo "$f depends on $d, a directory above $dir"
        status=1
      fi
    done
  done
done
# Nothing but the vernacular grammar is left at the top of src/.
for f in src/*.ml src/*.mli; do
  case "$f" in src/g_extraction.mli) continue ;; esac
  [[ -e "$f" ]] && { echo "$f is at the top of src/: put it in the directory of its stage"; status=1; }
done

for rule in "${rules[@]}"; do
  modules=${rule%% : *}
  forbidden=" ${rule##* : } "
  for m in $modules; do
    # ocamldep is silent about a missing file: a renamed module would drop
    # out of the check unnoticed.
    if [[ ! -f "src/$m.ml" ]]; then
      echo "src/$m.ml does not exist: update the rules"
      status=1
      continue
    fi
    for d in $(deps_of "src/$m.ml"); do
      if [[ "$forbidden" == *" $d "* ]]; then
        echo "src/$m.ml depends on $d, which its rule forbids"
        status=1
      fi
    done
  done
done

# A layering violation can be a dependency cycle, on which dune reports the
# cycle and then never exits: check the source first, build only a tree
# that passes.
if (( status )); then
  echo "not building: fix the dependencies above first"
  exit $status
fi

dune build --root . @src/check ./bin/printer_reads/main.exe 2>&1 | head -20
reach=$(./_build/default/bin/printer_reads/main.exe _build/default/src/.crane_plugin.objs/byte Emit__Print Base__Table) || {
  echo "bin/printer_reads failed"
  exit 1
}
printer_reads=$(printf '%s\n' "$reach" | cut -f1 | sort -u)
for r in $printer_reads; do
  if [[ " $PRINTER_TABLE_CONFIGURATION $PRINTER_TABLE_PENDING " != *" $r "* ]]; then
    echo "the printer reads Table.$r, a fact the declaration it prints should carry:"
    printf '%s\n' "$reach" | awk -F'\t' -v r="$r" '$1 == r { print "  " $2 }'
    status=1
  fi
done
for r in $PRINTER_TABLE_PENDING $PRINTER_TABLE_CONFIGURATION; do
  if [[ $'\n'"$printer_reads"$'\n' != *$'\n'"$r"$'\n'* ]]; then
    echo "the printer no longer reads Table.$r: delete it from PRINTER_TABLE_PENDING or PRINTER_TABLE_CONFIGURATION"
    status=1
  fi
done

# Nor does it read a plan's tables as global cells: what a plan decided for
# a declaration reaches the printer on the declaration's leaf, resolved
# (Unit_plan.Cpp_resolution's keys).  What it may still reach of the plan modules is
# listed, by module: the spelling configuration, what the position the
# printer enters is derived from (Unit_plan.Cpp_names.next: the file-scope names that
# withhold a function's qualifier; its out-of-line scope is resolved, on the
# function's frame) and the spelling of that scope (Core_plan.Scope_plan.qualifier).
# PENDING only shrinks.
PRINTER_PLAN_ALLOWED=(
  "Unit_plan__Cpp_state : file_start pp_tvar sn file_scope_aliases_of"
  "Core_plan__Module_plan : "
  "Core_plan__Scope_plan : qualifier"
)
PRINTER_PLAN_PENDING=(
  "Unit_plan__Cpp_state : "
  "Core_plan__Module_plan : "
  "Core_plan__Scope_plan : "
)
for i in "${!PRINTER_PLAN_ALLOWED[@]}"; do
  m=${PRINTER_PLAN_ALLOWED[$i]%% : *}
  allowed=" ${PRINTER_PLAN_ALLOWED[$i]##* : } ${PRINTER_PLAN_PENDING[$i]##* : } "
  reach=$(./_build/default/bin/printer_reads/main.exe _build/default/src/.crane_plugin.objs/byte Emit__Print "$m") || {
    echo "bin/printer_reads failed on $m"
    exit 1
  }
  reads=$(printf '%s\n' "$reach" | cut -f1 | sort -u)
  for r in $reads; do
    if [[ "$allowed" != *" $r "* ]]; then
      echo "the printer reads ${m//__/.}.$r, which the leaf it prints should carry resolved:"
      printf '%s\n' "$reach" | awk -F'\t' -v r="$r" '$1 == r { print "  " $2 }'
      status=1
    fi
  done
  for r in $allowed; do
    if [[ $'\n'"$reads"$'\n' != *$'\n'"$r"$'\n'* ]]; then
      echo "the printer no longer reads ${m//__/.}.$r: delete it from PRINTER_PLAN_ALLOWED or PRINTER_PLAN_PENDING"
      status=1
    fi
  done
done

# The printer decides no name.  A module's or a global's C++ name is decided
# the first time Common's renaming asks for it (mp_renaming_fun,
# ref_renaming_fun), and the decision recorded (note_decided_while_emitting);
# the printer reads names already decided -- resolved ones, or a decided
# lookup such as Common.decided_module_name -- and reaches none of the three.
for v in mp_renaming_fun ref_renaming_fun note_decided_while_emitting; do
  deciding=$(./_build/default/bin/printer_reads/main.exe _build/default/src/.crane_plugin.objs/byte Emit__Print Base__Common "$v") || {
    echo "bin/printer_reads failed on Common.$v"
    exit 1
  }
  if [[ -n "$deciding" ]]; then
    echo "the printer reaches Common.$v, which decides a name, by:"
    printf '%s\n' "$deciding" | sed 's/^/  /'
    status=1
  fi
done

exit $status
