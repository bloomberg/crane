(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A method whose result is an alias of a function type, [pred nat], with
    a body that takes the alias's argument too.  Its parameters are those
    its type declares, as a function's are, and the lambda the body takes
    beyond them is the closure it returns: it took them all, so it was
    declared [pred<Nat> runner(const Nat &s)], returning a [bool] as a
    [pred<Nat>], while its callers, reading its type, called [runner()] and
    applied the result. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module MethodReturnsFunctionAlias.
  Definition pred (A : Type) : Type := A -> bool.

  Definition always (b : bool) : pred nat := fun s => b.

  Module Holder.
    Record holder := { run : pred nat; tag : nat }.

    Definition runner (h : holder) : pred nat := fun s => run h s.
  End Holder.

  Module Tree.
    Inductive tree := Leaf | Node (l r : tree).

    Definition is_leaf (t : tree) : pred nat :=
      fun _ => match t with Leaf => true | _ => false end.
  End Tree.

  Definition t1 : bool := always true 0.
  Definition t2 : bool :=
    Holder.runner {| Holder.run := fun n => Nat.eqb n 0; Holder.tag := 1 |} 0.
  Definition t3 : bool := Tree.is_leaf Tree.Leaf 0.
  Definition t4 : bool := Tree.is_leaf (Tree.Node Tree.Leaf Tree.Leaf) 0.
End MethodReturnsFunctionAlias.

Crane Extraction "method_returns_function_alias" MethodReturnsFunctionAlias.
