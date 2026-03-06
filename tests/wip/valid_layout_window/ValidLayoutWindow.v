(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: layout bounds check against 12-bit address space. *)

From Stdlib Require Import Nat Bool.

Module ValidLayoutWindow.

Record layout : Type := mkLayout {
  base_addr : nat;
  code_size : nat
}.

Definition valid_layoutb (l : layout) : bool :=
  base_addr l + code_size l <=? 4096.

Definition t : nat :=
  (if valid_layoutb (mkLayout 128 256) then 1 else 0) +
  (if valid_layoutb (mkLayout 4090 20) then 1 else 0).

End ValidLayoutWindow.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "valid_layout_window" ValidLayoutWindow.
