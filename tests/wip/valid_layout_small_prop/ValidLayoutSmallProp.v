(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: valid_layout remains a Prop-valued layout predicate. *)

From Stdlib Require Import Nat.

Module ValidLayoutSmallProp.

Record layout : Type := mkLayout {
  base_addr : nat;
  code_size : nat
}.

Definition valid_layout (l : layout) : Prop :=
  base_addr l + code_size l <= 4096.

Definition t : Prop := valid_layout (mkLayout 4000 20).

End ValidLayoutSmallProp.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "valid_layout_small_prop" ValidLayoutSmallProp.
