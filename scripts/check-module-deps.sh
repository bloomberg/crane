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
FINISHING="Cpp_pipeline Loopify Loopify_analysis Loopify_tail Loopify_tmc Loopify_frame Cpp_depth Borrow_projection Cpp_erasure Function_entity Cpp_constants Cpp_local_closures Cpp_shared_args Cpp_simplify Cpp_temporaries Move_check Ownership_plan Return_moves Control_to_legacy_minicpp"

# layer modules : forbidden dependencies
rules=(
  "miniml minicpp foreign_template crane_rt tparam_kinds scheme ml_schema lexenv : $TRANSLATION $PRINTER $FINISHING Table Common"
  "cpp_pipeline loopify loopify_analysis loopify_tail loopify_tmc loopify_frame cpp_depth borrow_projection cpp_erasure function_entity cpp_constants cpp_local_closures cpp_shared_args cpp_simplify cpp_temporaries move_check ownership_plan return_moves control_to_legacy_minicpp : $TRANSLATION $PRINTER"
  # The printer reads Cpp_erasure's settled declarations; nothing else of the
  # finishing passes.
  "cpp_print : $TRANSLATION ${FINISHING/ Cpp_erasure/}"
)

# The printer reads Table for configuration and for spelling rules that are
# functions of a name alone, and to record the headers it writes for
# CRANE_CHECK_IR to compare with the planned demands; a fact about the
# program it is handed in the declaration, decided by a plan or a pass.  The
# facts it still asks Table for are listed, and the list only shrinks: a read
# that goes is deleted from it, and a new one is an error.  A custom's text
# is resolved with the declaration's names (Cpp_names.custom_text), and a
# mapping's element holes are decided at the seam
# (Cpp_erasure.instantiate_foreign).
PRINTER_TABLE_CONFIGURATION="Runtime erase_fn_header is_modfile std_lib modular non_atomic_rc arena_header escape_reserved_struct_name"
PRINTER_TABLE_PENDING=""

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
    # ocamldep is silent about a missing file: a renamed module would drop
    # out of the check unnoticed.
    if [[ ! -f "src/$m.ml" ]]; then
      echo "src/$m.ml does not exist: update the layer lists"
      status=1
      continue
    fi
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
