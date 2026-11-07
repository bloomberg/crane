#!/usr/bin/env bash
# Check the dependency direction between the plugin's layers: the IR does not
# depend on any pass, the finishing passes do not depend on translation or on
# the printer, and the printer depends on neither translation nor the passes
# that run before it.  Direct dependencies are checked; each layer obeying the
# rule keeps the transitive closure obeying it too.  The printer also asks
# Table nothing about the program beyond a list that only shrinks, wherever
# in the plugin the read is written (bin/printer_reads, which needs OCaml's
# compiler-libs, finds them).
#
# Usage: scripts/check-module-deps.sh   (from the repository root)
set -euo pipefail
cd "$(dirname "$0")/.."

TRANSLATION="Translation Translation_state Translation_support Translation_types Translation_calls Gen_decls Gen_context Gen_records Gen_instances Gen_functions Gen_inductives Plan_templates Cpp_leaf_plan Cpp_ind Cpp Extract_env Structure_analysis Method_registry"
PRINTER="Cpp_print"
FINISHING="Cpp_pipeline Loopify Loopify_analysis Loopify_tail Loopify_tmc Loopify_frame Cpp_depth Borrow_projection Cpp_erasure Function_entity Cpp_constants Cpp_local_closures Cpp_shared_args Cpp_simplify Cpp_temporaries Move_check Ownership_ir Return_moves Control_to_legacy_minicpp"

# layer modules : forbidden dependencies
rules=(
  "miniml minicpp foreign_template crane_rt tparam_kinds scheme ml_schema lexenv : $TRANSLATION $PRINTER $FINISHING Table Common"
  "cpp_pipeline loopify loopify_analysis loopify_tail loopify_tmc loopify_frame cpp_depth borrow_projection cpp_erasure function_entity cpp_constants cpp_local_closures cpp_shared_args cpp_simplify cpp_temporaries move_check ownership_ir return_moves control_to_legacy_minicpp : $TRANSLATION $PRINTER"
  # The printer reads Cpp_erasure's settled declarations; nothing else of the
  # finishing passes.
  "cpp_print : $TRANSLATION ${FINISHING/ Cpp_erasure/}"
)

# The printer reads Table for configuration and for spelling rules that are
# functions of a name alone (what it records under CRANE_CHECK_IR -- the
# headers and customs it writes -- it records in an oracle's branch); a fact
# about the program it is handed in the declaration, decided by a plan or a
# pass.  The
# facts it still asks Table for are listed, and the list only shrinks: a read
# that goes is deleted from it, and a new one is an error.
#
# A read counts wherever it is written: in cpp_print.ml (which opens Table,
# so a read need not be qualified), or in any value of the plugin a value of
# cpp_print.ml reaches.  bin/printer_reads lists them from the typed trees
# dune writes, with a shortest chain each; a read in the branch of an
# [if Probe.checking () then] is an oracle's and does not count.  The graph
# does not follow control flow, so a read the printer reaches only through a
# closure it hands the resolver (Cpp_names.named's [live]) counts too.
PRINTER_TABLE_CONFIGURATION="arena_header erase_fn_header escape_reserved_struct_name modular std_lib register_census lang modpath_of_r repr_of_r safe_basename_of_global string_of_modfile mp_length base_mp at_toplevel is_toplevel common_prefix_from_list"
# Inductive classification (frozen from planning on: Table.inductives is
# counted by the census) and custom texts, read while naming (Cpp_names,
# Common).
PRINTER_TABLE_PENDING="get_ind_nb_ctors_opt get_record_fields is_any_inline_custom is_custom is_enum_inductive is_typeclass promoted_inductives to_inline written_custom_text written_inline_custom_text"

status=0
dune build --root . @src/check ./bin/printer_reads/main.exe 2>&1 | head -20
reach=$(./_build/default/bin/printer_reads/main.exe _build/default/src/.crane_plugin.objs/byte Cpp_print Table) || {
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
