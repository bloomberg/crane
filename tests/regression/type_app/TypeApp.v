(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*
   This test tries to expose the TODO at extraction.ml:501-503:
   "Type application isn't happening/reducing in instances where not needed for OCaml.
    Type variables that are semantically instantiated in Rocq are appearing in
    extracted code at the term level."

   This involves polymorphic functions where type instantiation should happen
   but might not be reducing properly.
*)
Require Import Crane.Mapping.NatInt.
Require Crane.Extraction.

Module TypeApp.

(* Identity function - should have type instantiated at call sites *)
Definition id {A : Type} (x : A) : A := x.

(* Use id with different types - type args should be instantiated *)
Definition id_int := id 42.
Definition id_bool := id true.

(* Compose polymorphic functions *)
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) (x : A) : C :=
  g (f x).

(* Type instantiation in nested contexts *)
Definition nested_poly {A : Type} (x : A) : A :=
  id (id (id x)).

(* Polymorphic list operations *)
Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} _ _.

Fixpoint map {A B : Type} (f : A -> B) (l : list A) : list B :=
  match l with
  | nil => nil
  | cons x xs => cons (f x) (map f xs)
  end.

(* Map with explicit type applications *)
Definition test_map := map (fun x => x + 1) (cons 1 (cons 2 (cons 3 nil))).

(* Partial application of polymorphic functions *)
Definition map_succ := map (fun x => x + 1).

Definition test_map_succ := map_succ (cons 5 (cons 6 nil)).

(* Higher-order polymorphic function *)
Definition twice {A : Type} (f : A -> A) (x : A) : A :=
  f (f x).

Definition test_twice := twice (fun x => x + 1) 10.

(* Type application in module type with polymorphic operations *)
Module Type Monoid.
  Parameter T : Type.
  Parameter empty : T.
  Parameter append : T -> T -> T.
End Monoid.

Module NatMonoid <: Monoid.
  Definition T := nat.
  Definition empty := 0.
  Definition append := Nat.add.
End NatMonoid.

(* Functor using a monoid - type applications should resolve *)
Module UseMonoid (M : Monoid).
  Definition combine_empty : M.T := M.append M.empty M.empty.
  Definition triple (x : M.T) : M.T := M.append x (M.append x x).
End UseMonoid.

Module NatMonoidUser := UseMonoid NatMonoid.
Definition monoid_test := NatMonoidUser.combine_empty.

End TypeApp.

Crane Extraction "type_app" TypeApp.
