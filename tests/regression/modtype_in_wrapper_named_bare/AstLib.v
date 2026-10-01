(** Crane bug: a module type declared inside a collision wrapper is emitted
    nowhere.

    A file whose child module's name collides with an inductive elsewhere is
    emitted as a struct named after the file, and its other children are
    written inside it.  A module type is a concept, and C++ has no member
    concepts, so a concept cannot be written there -- and rather than being
    hoisted to namespace scope, where it could be, it is dropped.  Nothing
    then declares the name the functor below constrains its parameter with.

    [bystander_named_bare] is this file with the module type in a file of its
    own, which is the position where it works. *)

From Crane Require Import Mapping.Std.
From Stdlib Require Import Arith PeanoNat.
From CraneTestsRegression Require Import modtype_in_wrapper_named_bare.Rid.

(** Colliding: its capitalised label is [Coll]'s inductive, so it fires the
    wrapper -- and the printer flattens it into the wrapper's body. *)
Module Collider.
  Definition pick (a b : nat) : nat := if Nat.leb a b then b else a.
End Collider.

(** The defect: a module type among the wrapper's children.  It has no place
    in the struct and is given none outside it either. *)
Module Type Ord.
  Parameter t : Set.
  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.
End Ord.

(** Not colliding: the printer nests it inside the same wrapper struct. *)
Module RawIDOrd <: Ord.
  Definition t : Set := raw_id.
  Definition eq_dec : forall x y : t, {x = y} + {x <> y} := raw_id_dec.
End RawIDOrd.
