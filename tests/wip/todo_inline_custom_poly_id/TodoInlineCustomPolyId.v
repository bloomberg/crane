(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: inlined polymorphic function symbols should not mis-handle eta expansion. *)

From Stdlib Require Import Nat Bool.

Module TodoInlineCustomPolyId.

Parameter foreign_id : forall {A : Type}, A -> A.

Definition test_value : nat :=
  let alias := @foreign_id in
  let kept_nat := alias nat 4 in
  let kept_bool := alias bool true in
  if kept_bool then S kept_nat else 0.

End TodoInlineCustomPolyId.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extract Inlined Constant TodoInlineCustomPolyId.foreign_id => "inline_id_impl" From "todo_inline_custom_poly_id_support.h".
Crane Extraction "todo_inline_custom_poly_id" TodoInlineCustomPolyId.
