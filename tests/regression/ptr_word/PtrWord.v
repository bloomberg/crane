(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** [Set Crane SharedVariant]: a block address is held as a pointer and swapped
    a word at a time, so that it keeps its capability on targets where a
    pointer is more than its address bits (such as Fil-C). *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module PtrWord.

Inductive tree : Type := Leaf | Node (l r : tree).

Fixpoint size (t : tree) : nat :=
  match t with Leaf => 1 | Node l r => size l + size r end.

Definition sample : nat := size (Node (Node Leaf Leaf) Leaf).

End PtrWord.

Set Crane SharedVariant.
Crane Extraction "ptr_word" PtrWord.
