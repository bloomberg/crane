(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Edge cases for block template (%result) expansion.
    Tests unusual type combinations and nested block templates. *)

From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatInt Monads.ITree Monads.IO.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

Local Open Scope pstring_scope.

(** Custom block template axioms for testing *)

Axiom read_bool : forall {E} `{consoleE -< E}, itree E bool.
#[global] Instance read_bool_mapping : OperationMapping (Ref (@read_bool)) :=
  effect_cpp ["iostream"] []
    (WithBody "" "%result = true").

Module BlockTemplateEdge.

(** 1. Block template result used immediately in if-then-else *)
Definition block_in_if : itree ioE string :=
  b <- read_bool ;;
  Ret (if b then "yes" else "no").

(** 2. Block template result used in arithmetic *)
Definition block_in_arith : itree ioE int :=
  n <- get_line ;;
  Ret (PrimInt63.add (PrimString.length n) 1).

(** 3. Two block templates of same type back-to-back *)
Definition two_strings : itree ioE string :=
  a <- get_line ;;
  b <- get_line ;;
  Ret (cat a b).

(** 4. Block template result bound but unused *)
Definition block_unused : itree ioE nat :=
  _ <- get_line ;;
  Ret 42.

(** 5. Block template followed by non-block operation *)
Definition block_then_pure : itree ioE int :=
  s <- get_line ;;
  let n := PrimString.length s in
  Ret (PrimInt63.add n n).

End BlockTemplateEdge.

Crane Extraction "block_template_edge" BlockTemplateEdge.
