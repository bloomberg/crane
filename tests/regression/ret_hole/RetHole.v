(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [%ret] in an inline mapping spells the type the call yields, as
    translation recorded it.  Only a template applied as a call yields one:
    a block template ([%result]) naming [%ret] is refused before anything is
    printed, where it used to leave the placeholder in the C++ text. *)

From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Crane Require Import Extraction.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.
From Crane.Mapping Require Import Std NatInt.

Axiom double : nat -> nat.
#[global] Instance double_mapping : OperationMapping (Ref (@double)) :=
  pure_cpp [] ["x0"]
    (Expr "static_cast<%ret>(2 * %arg(x0))").

Module RetHole.

Definition quadruple (n : nat) : nat := double (double n).

End RetHole.
Crane Extraction "ret_hole" RetHole.

Axiom halve : nat -> nat.
#[global] Instance halve_mapping : OperationMapping (Ref (@halve)) :=
  pure_cpp [] ["x0"]
    (WithBody "" "%result = static_cast<%ret>(%arg(x0) / 2)").

Module RetInBlock.

Definition quarter (n : nat) : nat := halve (halve n).

End RetInBlock.
Fail Crane Extraction "ret_hole_in_block" RetInBlock.
