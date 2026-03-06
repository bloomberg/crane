(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: update_nth preserves list length after in-bounds patch. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module DecodeAddWfEdge0063.

Definition update_nth {A} (n : nat) (x : A) (l : list A) : list A :=
  if n <? length l
  then firstn n l ++ x :: skipn (S n) l
  else l.

Definition t : nat := length (update_nth 2 9 [1; 2; 3; 4]).

End DecodeAddWfEdge0063.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "decode_add_wf_edge_0063" DecodeAddWfEdge0063.
