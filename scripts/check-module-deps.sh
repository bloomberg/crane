#!/usr/bin/env bash
# Check the dependency direction between the plugin's layers: the IR does not
# depend on any pass, the finishing passes do not depend on translation or on
# the printer, and the printer depends on neither translation nor the passes
# that run before it.  Direct dependencies are checked; each layer obeying the
# rule keeps the transitive closure obeying it too.  The printer also asks
# Table nothing about the program beyond a list that only shrinks.
#
# Usage: scripts/check-module-deps.sh   (from the repository root)
set -euo pipefail
cd "$(dirname "$0")/.."

TRANSLATION="Translation Translation_state Translation_support Translation_types Translation_calls Gen_decls Gen_context Gen_records Gen_instances Gen_functions Gen_inductives Plan_templates Cpp_ind Cpp Extract_env Structure_analysis Method_registry"
PRINTER="Cpp_print"
FINISHING="Cpp_pipeline Loopify Loopify_analysis Loopify_tail Loopify_tmc Loopify_frame Last_use Cpp_depth Borrow_projection Cpp_erasure Function_entity"

# layer modules : forbidden dependencies
rules=(
  "miniml minicpp foreign_template crane_rt tparam_kinds scheme ml_schema lexenv : $TRANSLATION $PRINTER $FINISHING Table Common"
  "cpp_pipeline loopify loopify_analysis loopify_tail loopify_tmc loopify_frame last_use cpp_depth borrow_projection cpp_erasure function_entity : $TRANSLATION $PRINTER"
  # The printer reads Cpp_erasure's settled declarations; nothing else of the
  # finishing passes.
  "cpp_print : $TRANSLATION ${FINISHING/ Cpp_erasure/}"
)

# The printer reads Table for configuration and for spelling rules that are
# functions of a name alone, and to record the headers it writes for
# CRANE_CHECK_IR to compare with the planned demands; a fact about the
# program it is handed in the declaration, decided by a plan or a pass.  The
# facts it still asks Table for are listed, and the list only shrinks: a read
# that goes is deleted from it, and a new one is an error.
PRINTER_TABLE_CONFIGURATION="Runtime erase_fn_header is_modfile std_lib modular non_atomic_rc arena_header escape_reserved_struct_name"
PRINTER_TABLE_PENDING="is_boxed_recursive_ind find_boxed_wrapper_opt get_ind_nb_ctors_opt custom_info"

status=0
printer_reads=$(grep -o 'Table\.[a-zA-Z_]*' src/cpp_print.ml | sed 's/^Table\.//' | sort -u)
for r in $printer_reads; do
  if [[ " $PRINTER_TABLE_CONFIGURATION $PRINTER_TABLE_PENDING " != *" $r "* ]]; then
    echo "src/cpp_print.ml reads Table.$r, a fact the declaration it prints should carry"
    status=1
  fi
done
for r in $PRINTER_TABLE_PENDING; do
  if [[ $'\n'"$printer_reads"$'\n' != *$'\n'"$r"$'\n'* ]]; then
    echo "src/cpp_print.ml no longer reads Table.$r: delete it from PRINTER_TABLE_PENDING"
    status=1
  fi
done

for rule in "${rules[@]}"; do
  modules=${rule%% : *}
  forbidden=" ${rule##* : } "
  for m in $modules; do
    deps=$(ocamlfind ocamldep -modules "src/$m.ml" | cut -d: -f2)
    for d in $deps; do
      if [[ "$forbidden" == *" $d "* ]]; then
        echo "src/$m.ml depends on $d, which its layer may not use"
        status=1
      fi
    done
  done
done
exit $status
