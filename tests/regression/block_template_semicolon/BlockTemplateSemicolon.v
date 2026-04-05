(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Test: Block template (%result) with semicolons in string arguments.

   The Sblock_custom rendering in cpp_print.ml splits the rendered body
   on ';' to produce separate statements. If a string argument passed to
   the template contains a semicolon, the split could break the string
   literal across multiple "statements."

   Example: read_trimmed "a;b" should produce:
     { std::ifstream _f("a;b"s); std::getline(_f, s); }
   NOT:
     { std::ifstream _f("a;
     b"s);
     std::getline(_f, s);
     };
*)
From Corelib Require Import PrimString.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO.

(** Block template with %a0 that will receive a string containing ';' *)
Axiom read_trimmed : forall {E} `{fileE -< E}, string -> itree E string.
Crane Extract Inlined Constant read_trimmed =>
  "{ std::ifstream _f(%a0); std::getline(_f, %result); }" From "fstream".

Module BlockTemplateSemicolon.

  (** String argument with semicolons in expression position (monad right identity)
      Tests gen_block_iife semicolon splitting *)
  Definition read_semicolon_expr : itree ioE string :=
    s <- read_trimmed "path;with;semicolons" ;;
    Ret s.

  (** String argument with semicolons in statement position (bind with computation)
      Tests Sblock_custom semicolon splitting *)
  Definition read_semicolon_stmt : itree ioE string :=
    s <- read_trimmed "path;with;semicolons" ;;
    Ret (cat s " done").

  (** String argument with no semicolons (control case) *)
  Definition read_normal : itree ioE string :=
    s <- read_trimmed "normal_path.txt" ;;
    Ret (cat s " ok").

End BlockTemplateSemicolon.

Crane Extraction "block_template_semicolon" BlockTemplateSemicolon.
