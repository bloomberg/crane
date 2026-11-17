(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** A recursive type of a unit with both the scoped arena and non-atomic
    reference counts: its constructors allocate a child through the
    non-atomic pointer's own arena-aware factory, [crane::rc<T>::make]. *)

Module ArenaNonAtomicRc.

Inductive tree : Type :=
| leaf : tree
| node : tree -> nat -> tree -> tree.

Fixpoint size (t : tree) : nat :=
  match t with
  | leaf => 1
  | node l _ r => 1 + size l + size r
  end.

Fixpoint mirror (t : tree) : tree :=
  match t with
  | leaf => leaf
  | node l x r => node (mirror r) x (mirror l)
  end.

End ArenaNonAtomicRc.

Require Crane.Extraction.
Set Crane Arena.
Set Crane NonAtomicRc.
Crane Extraction "arena_non_atomic_rc" ArenaNonAtomicRc.
