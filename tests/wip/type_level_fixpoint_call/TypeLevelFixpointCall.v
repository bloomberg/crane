From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.
(** WIP: A `Fixpoint` returning `Type` erases to `std::any`; a value of type `ty 1`
    is then applied as a function, and `std::any` provides no call operator. *)

Module TypeLevelFixpointCall.
Fixpoint ty (n : nat) : Type := match n with O => nat | S m => (nat -> ty m)%type end.
Definition v1 : ty 1 := fun n => n + 1.
Definition go : nat := (v1 : nat -> ty 0) 4.
End TypeLevelFixpointCall.
Crane Extraction "type_level_fixpoint_call" TypeLevelFixpointCall.
