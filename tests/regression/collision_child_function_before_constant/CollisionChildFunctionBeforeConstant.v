(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The child module [List] collides with the [List] struct the standard
    library's [list] is written as, so the file is written inside a struct
    of its own name, the child flattened into it.  The constant [c] is
    initialised from the child's [first], and an initialiser is no
    complete-class context: [first] has to be declared ahead of [c], where
    the child is, not after every element of the file. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.

Module List.
  Definition first (l : list nat) : nat := match l with nil => 0 | x :: _ => x end.
End List.

Definition c : nat := List.first (5 :: nil).

Crane Extraction "collision_child_function_before_constant" c.
