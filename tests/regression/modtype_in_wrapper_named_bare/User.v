From Crane Require Import Mapping.Std.
From CraneTestsRegression Require Import modtype_in_wrapper_named_bare.Coll.
From CraneTestsRegression Require Import modtype_in_wrapper_named_bare.Rid.
From CraneTestsRegression Require Import modtype_in_wrapper_named_bare.AstLib.
From CraneTestsRegression Require Import modtype_in_wrapper_named_bare.MkTbl.

(** The control: the bystander named through a [::] reference. *)
Definition viaQualified (a b : raw_id) : bool :=
  if AstLib.RawIDOrd.eq_dec a b then true else false.

(** The defect: the same bystander named bare, as a functor argument. *)
Module RM := MkTbl.Make AstLib.RawIDOrd.
Definition start : RM.tbl bool := RM.empty bool.

Definition viaColliding (a b : nat) : nat := AstLib.Collider.pick a b.

(** Keeps [Coll.Collider] alive, so the collision it causes is real. *)
Definition keepColl (r : Coll.Collider) : nat :=
  match r with Coll.Tag0 => 0 | Coll.Tag1 n => n end.

Crane Extraction "modtype_in_wrapper_named_bare" viaQualified start viaColliding keepColl.
