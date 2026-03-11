(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: dependent aliases should preserve substituted carrier types. *)

From Stdlib Require Import Nat.

Module TodoTypeSubstPackAlias.

Record Pack := mkPack {
  carrier : Type;
  seed : carrier;
  step : carrier -> carrier
}.

Definition step_of (p : Pack) : carrier p -> carrier p :=
  step p.

Definition run_twice (p : Pack) : carrier p :=
  let alias := step_of p in
  alias (alias (seed p)).

Definition nat_pack : Pack :=
  mkPack nat 3 S.

Definition test_value : nat :=
  run_twice nat_pack.

End TodoTypeSubstPackAlias.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "todo_type_subst_pack_alias" TodoTypeSubstPackAlias.
