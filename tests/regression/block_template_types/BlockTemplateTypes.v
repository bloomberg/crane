(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Regression test for block template (%result) type inference.

   Verifies that %result expansion emits the correct C++ type declaration
   for non-string return types: unsigned int (nat), bool, and mixed.
*)
From Corelib Require Import PrimString.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO.

Local Open Scope pstring_scope.

(** Block templates returning non-string types. *)

Axiom read_nat : forall {E} `{consoleE -< E}, itree E nat.
Crane Extract Inlined Constant read_nat => "std::cin >> %result".

Axiom is_positive : forall {E} `{consoleE -< E}, nat -> itree E bool.
Crane Extract Inlined Constant is_positive => "%result = (%a0 > 0u)".

Axiom parse_nat : forall {E} `{consoleE -< E}, string -> itree E nat.
Crane Extract Inlined Constant parse_nat =>
  "%result = static_cast<unsigned int>(std::stoul(%a0))".

Module BlockTemplateTypes.

  (** %result inferred as [unsigned int]. *)
  Definition test_read_nat : itree iIO nat :=
    n <- read_nat ;;
    Ret (n + 1).

  (** %result inferred as [bool], with [unsigned int] in same scope. *)
  Definition test_is_positive : itree iIO string :=
    n <- read_nat ;;
    b <- is_positive n ;;
    Ret (if b then "positive" else "zero").

  (** %result inferred as [unsigned int] from [string] argument.
      Tests %a0 and %result together with nat return type. *)
  Definition test_parse_nat : itree iIO nat :=
    s <- get_line ;;
    n <- parse_nat s ;;
    Ret (n + 2).

  (** Three different block template types in one function:
      [std::string] (get_line), [unsigned int] (read_nat), [bool] (is_positive). *)
  Definition test_mixed : itree iIO string :=
    name <- get_line ;;
    n <- read_nat ;;
    b <- is_positive n ;;
    Ret (cat name (if b then " wins" else " loses")).

  (** Two [unsigned int] block templates with arithmetic on results. *)
  Definition test_nat_arith : itree iIO nat :=
    a <- read_nat ;;
    b <- read_nat ;;
    Ret (a + b).

End BlockTemplateTypes.

Crane Extraction "block_template_types" BlockTemplateTypes.
