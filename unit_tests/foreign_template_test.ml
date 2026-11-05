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
  check "implicit arguments" (custom_template_with_args "Sum1" 2 = "Sum1<%t0, %t1>");
  let std_pair = "const auto& [%b0a0, %b0a1] = %scrut; %br0" in
  check "binding by reference" (structured_binding std_pair = Some By_reference);
  check "binding by value" (structured_binding "auto [%b0a0, %b0a1] = %scrut; %br0" = Some By_value);
  check "binding, spaced" (structured_binding "const auto &[ %b0a0 , %b0a1 ] =\n  %scrut;\n  %br0" = Some By_reference);
  check "binding of three" (structured_binding "auto [%b0a0, %b0a1, %b0a2] = %scrut; %br0" = Some By_value);
  check "binders out of order" (structured_binding "auto [%b0a1, %b0a0] = %scrut; %br0" = None);
  check "not a binding" (structured_binding "auto& p = %scrut; auto %b0a0 = p.first; %br0" = None);
  check "something after the branch" (structured_binding "auto [%b0a0] = %scrut; %br0 f();" = None);
  check "bound by value" (bound_by_value std_pair = "auto [%b0a0, %b0a1] = %scrut; %br0");
  check "declared: a qualified template" (declared_type_names "std::vector<%t2> *" = ["std::vector"]);
  check "declared: builtin words" (declared_type_names "const unsigned long long" = []);
  check "declared: holes only" (declared_type_names "%t1" = []);
  check "declared: a member of a hole" (declared_type_names "typename %t0::value_type" = []);
  check "declared: each name" (declared_type_names "std::pair<mpz_class, %elem>" = ["std::pair"; "mpz_class"]);
  check "declared: digits are not names" (declared_type_names "std::array<int, 4>" = ["std::array"]);
  let standard s = standard_names_written (term_template s) in
  check "standard: a call" (standard "std::max(%a0, %a1)" = [("std::max", "algorithm")]);
  check "standard: each once, sorted"
    (standard "std::move(%a0) + std::to_string(std::move(%a1))" = [("std::move", "utility"); ("std::to_string", "string")]);
  check "standard: a nested namespace" (standard "std::chrono::milliseconds(%a0)" = [("std::chrono", "chrono")]);
  check "standard: not another std" (standard "crane::std::max(%a0) + mystd::max(%a1)" = []);
  check "standard: an unknown name" (standard "std::frobnicate(%a0)" = []);
  check "standard: holes are not text" (standard "%a0.size()" = []);
  let stmts s =
    List.map (List.filter (( <> ) (CCstring ""))) (statements (term_template (with_result "_r" s)))
  in
  check "statements: one per semicolon, trimmed"
    (stmts " _r = %a0;  f(_r) ;" = [[CCstring "_r = "; CCarg 0]; [CCstring "f(_r)"]]);
  check "statements: a last one without its semicolon" (stmts "std::cin >> _r" = [[CCstring "std::cin >> _r"]]);
  check "statements: a for header is one statement"
    (stmts "for (int i = 0;; ++i) { if (i >= %a0) break; }"
     = [[CCstring "for (int i = 0;; ++i) { if (i >= "; CCarg 0; CCstring ") break"]; [CCstring "}"]]);
  check "statements: not inside a literal" (stmts "f(\";\"); g(';')" = [[CCstring "f(\";\")"]; [CCstring "g(';')"]]);
  check "statements: blank ones dropped" (stmts "a;; ;b" = [[CCstring "a"]; [CCstring "b"]]);
  check "statements: a hole alone" (stmts "%a0; %a1" = [[CCarg 0]; [CCarg 1]])
