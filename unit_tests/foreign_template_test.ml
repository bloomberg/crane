(* The placeholder parser: what a mapping's text means, token by token. *)

open Crane_plugin
open Foreign_template

let check name cond =
  if not cond then (
    Printf.eprintf "foreign_template: %s\n" name;
    exit 1 )

let () =
  check "fst is a projection" (is_pair_projection "%a0.first");
  check "snd is a projection" (is_pair_projection "%a0.second");
  check "a call is not" (not (is_pair_projection "f(%a0.first)"));
  check "another argument is not" (not (is_pair_projection "%a1.first"));
  check "term holes"
    (List.filter (( <> ) (CCstring "")) (term_template "std::make_pair<%t0>(%a0, %a1)")
     = [CCstring "std::make_pair<"; CCty_arg 0; CCstring ">("; CCarg 0;
        CCstring ", "; CCarg 1; CCstring ")"]);
  check "match holes"
    (List.mem CCscrut (match_template "if (%scrut) { %br0 } else { %br1 }")
     && List.mem (CCbody 1) (match_template "if (%scrut) { %br0 } else { %br1 }"));
  check "result" (with_result "_r" "%result = %a0;" = "_r = %a0;");
  check "drain"
    (drain_template "while (!%scrut.empty()) { %yield(f(x)); }"
     = [Drain_text "while (!%scrut.empty()) { "; Drain_yield "f(x)"; Drain_text "; }"]);
  check "implicit arguments" (custom_template_with_args "Sum1" 2 = "Sum1<%t0, %t1>")
