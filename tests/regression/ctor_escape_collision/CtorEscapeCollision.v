(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Repro: constructor escaping collision in generated enum-like forms. *)

From Stdlib Require Import Nat.

Module CtorEscapeCollision.

Inductive item : Type :=
| D'
| D_
| D''
| D__
| D'_
| D_'.

Definition tag (x : item) : nat :=
  match x with
  | D' => 1
  | D_ => 2
  | D'' => 3
  | D__ => 4
  | D'_ => 5
  | D_' => 6
  end.

Definition t : nat := tag D' + tag D_ + tag D'' + tag D__ + tag D'_ + tag D_'.

End CtorEscapeCollision.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Crane Extraction "ctor_escape_collision" CtorEscapeCollision.
