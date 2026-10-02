#!/usr/bin/env bash
# Check the dependency direction between the plugin's layers: the IR does not
# depend on any pass, the finishing passes do not depend on translation or on
# the printer, and the printer depends on neither translation nor the passes
# that run before it.  Direct dependencies are checked; each layer obeying the
# rule keeps the transitive closure obeying it too.
#
# Usage: scripts/check-module-deps.sh   (from the repository root)
set -euo pipefail
cd "$(dirname "$0")/.."

TRANSLATION="Translation Translation_state Translation_support Translation_types Translation_calls Gen_decls Cpp_ind Cpp Extract_env Structure_analysis Method_registry"
PRINTER="Cpp_print"
FINISHING="Cpp_pipeline Loopify Loopify_analysis Loopify_tail Loopify_tmc Loopify_frame Last_use Cpp_depth Borrow_projection Cpp_erasure Function_entity"

# layer modules : forbidden dependencies
rules=(
  "miniml minicpp foreign_template crane_rt tparam_kinds : $TRANSLATION $PRINTER $FINISHING Table Common"
  "cpp_pipeline loopify loopify_analysis loopify_tail loopify_tmc loopify_frame last_use cpp_depth borrow_projection cpp_erasure function_entity : $TRANSLATION $PRINTER"
  # The printer reads Cpp_erasure's settled declarations; nothing else of the
  # finishing passes.
  "cpp_print : $TRANSLATION ${FINISHING/ Cpp_erasure/}"
)

status=0
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
