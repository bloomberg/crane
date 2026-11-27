(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A file whose module [Sub] declares an inductive [tree], emitted as the
    struct [Tree] nested in [Sub]'s struct. *)

From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.

Module Sub.
  Inductive tree : Type :=
  | Leaf : tree
  | Node : tree -> nat -> tree -> tree.

  Fixpoint size (t : tree) : nat :=
    match t with Leaf => 0 | Node l _ r => S (size l + size r) end.
End Sub.
