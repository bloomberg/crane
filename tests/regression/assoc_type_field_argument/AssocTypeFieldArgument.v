From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.
Import ListNotations.

Module AssocTypeFieldArgument.

(** A class's associated [Type] field used as an argument type: the call
    site builds the argument at the erased shape ([pair<any, any>]) while the
    callee expects the instance's concrete element type. *)
Class Coll (C : Type) := {
  elt : Type ;
  empty : C ;
  insert : elt -> C -> C ;
  size : C -> nat
}.

#[export] Instance CNat : Coll (list nat) := {
  elt := nat ;
  empty := [] ;
  insert := fun x c => x :: c ;
  size := fun c => List.length c
}.

#[export] Instance CPair : Coll (list (nat * nat)) := {
  elt := (nat * nat)%type ;
  empty := [] ;
  insert := fun x c => x :: c ;
  size := fun c => List.length c
}.

Definition build3 {C : Type} `{Coll C} (a b c : elt) : C :=
  insert a (insert b (insert c empty)).

Definition total : nat :=
  @size (list nat) CNat (@build3 (list nat) CNat 1 2 3)
  + @size (list (nat * nat)) CPair
      (@build3 (list (nat * nat)) CPair (1,1) (2,2) (3,3)).

End AssocTypeFieldArgument.
Crane Extraction "assoc_type_field_argument" AssocTypeFieldArgument.
