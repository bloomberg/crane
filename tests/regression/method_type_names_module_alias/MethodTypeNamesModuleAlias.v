(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A function of a nested module whose type names one of the module's type
    aliases stays a function: the eponymous type's struct, where a method is
    written, is ahead of the alias.  The module's frame kept it one, but the
    registry's scan still made it a method.  For the eponymous record that
    meant calls written as calls of a method the record never got, and the
    function written nowhere ([Bag{...}.get()]); for the eponymous inductive,
    a method naming the alias inside the struct declared ahead of it
    ([size count() const] before [using size = Nat]). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module MethodTypeNamesModuleAlias.
  Module Bag.
    Record bag := { a : nat; n : nat }.
    Definition flag := bool.
    Definition get (b : bag) : flag := Nat.eqb (a b) 0.
  End Bag.

  Module Tree.
    Inductive tree := Leaf | Node (l r : tree).
    Definition size := nat.
    Fixpoint count (t : tree) : size :=
      match t with Leaf => 1 | Node l r => count l + count r end.
  End Tree.

  Definition use : bool := Bag.get {| Bag.a := 0; Bag.n := 3 |}.
  Definition leaves : nat := Tree.count (Tree.Node Tree.Leaf Tree.Leaf).
End MethodTypeNamesModuleAlias.

Crane Extraction "method_type_names_module_alias" MethodTypeNamesModuleAlias.
