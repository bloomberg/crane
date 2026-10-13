(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A call that writes only some of its callee's type arguments, and a
    polymorphic global used as a value with none written.  The supplied
    arguments keep their variables; the rest are open, to be found from the
    values or left to deduction -- never a neighbour's argument.
    - [bindo {A B}] applied to one type argument, then its values.
    - [liftO], a monadic map through a class over a type constructor, named
      with its carrier only.
    - [List.map] handed the bare polymorphic [twice]. *)

From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module TyargPartialTypeApplication.

Definition bindo {A B : Type} (o : option A) (k : A -> option B) : option B :=
  match o with Some a => k a | None => None end.

Definition bind_nat := @bindo nat.

Definition bound : option bool := bind_nat bool (Some 3) (fun n => Some (Nat.eqb n 3)).

Class Mon (M : Type -> Type) := {
  ret : forall {A}, A -> M A;
  bnd : forall {A B}, M A -> (A -> M B) -> M B
}.

#[export] Instance Mon_option : Mon option := {
  ret := fun _ a => Some a;
  bnd := fun _ _ o k => match o with Some a => k a | None => None end
}.

Definition liftO {M : Type -> Type} `{Mon M} {A B : Type} (f : A -> B) (m : M A) : M B :=
  bnd m (fun a => ret (f a)).

Definition lift_opt := @liftO option _.

Definition lifted : option nat := lift_opt nat nat S (Some 4).

Definition twice {A : Type} (x : A) : A * A := (x, x).

Definition doubled : list (nat * nat) := map twice [1; 2].

Definition first_of_doubled : nat :=
  match doubled with (a, _) :: _ => a | [] => 0 end.

End TyargPartialTypeApplication.

Crane Extraction "tyarg_partial_type_application" TyargPartialTypeApplication.
