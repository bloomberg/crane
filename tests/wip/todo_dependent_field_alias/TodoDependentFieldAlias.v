(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: dependent record field aliases should preserve substituted types. *)

From Stdlib Require Import Nat.

Module TodoDependentFieldAlias.

Record Magma := mkMagma {
  carrier : Type;
  op : carrier -> carrier -> carrier
}.

Definition nat_magma : Magma :=
  mkMagma nat Nat.add.

Definition pick_op (M : Magma) : carrier M -> carrier M -> carrier M :=
  op M.

Definition test_value : nat :=
  let alias := pick_op nat_magma in
  alias 2 3.

End TodoDependentFieldAlias.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "todo_dependent_field_alias" TodoDependentFieldAlias.
