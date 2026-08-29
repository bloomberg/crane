From Stdlib Require Import Lists.List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module HktClassParam.
  (** A type class parameterised over a type {i constructor} ([C : Type -> Type]).
      Crane emits the instance's methods against the shared [List] type but
      erases the element type, producing [List<std::any>] parameters where
      [List<Nat>] is required, which corrupts the mapped [List] type itself. *)
  Class Container (C : Type -> Type) := {
    empty : forall A, C A;
    insert : forall A, A -> C A -> C A;
    toList : forall A, C A -> list A
  }.

  Instance ListContainer : Container list := {
    empty := fun A => @nil A;
    insert := fun A x xs => x :: xs;
    toList := fun A xs => xs
  }.

  Definition build {C} `{Container C} (l : list nat) : C nat :=
    fold_right (fun n acc => insert nat n acc) (empty nat) l.

  Definition run (k : nat) : nat :=
    length (toList nat (build (C:=list) [1;2;3])) + k.
End HktClassParam.

Crane Extraction "hkt_class_param" HktClassParam.
